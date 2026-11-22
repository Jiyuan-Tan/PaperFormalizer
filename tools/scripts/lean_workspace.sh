#!/usr/bin/env bash
# The file work behind per-run Lake workspaces (`src/shared/workspace.ts` decides when and where):
#
#     lean_workspace.sh pack  <toolkit> <out.tar.zst> <lib> <papers lib> <staging>
#         one GENERATION of the toolkit as one archive: its pinned sources (every top-level `.lean`
#         but the papers' barrel, the library's directory without its staging tree, lakefile.toml,
#         lake-manifest.json, lean-toolchain) and their build outputs (`.lake/build/{lib/lean,ir}/<root>{,.*}`
#         for each of those roots, and `.lake/build/bin`; never a `.setup.json`, below). Written beside
#         <out> and renamed onto it.
#     lean_workspace.sh unpack <out.tar.zst> <node gen dir>
#         that archive unpacked once on this machine (under a lock; keeps the newest 3 generations;
#         what is unchanged since the previous one, hard links to its files: `dedupe`)
#     lean_workspace.sh pin <node gen dir> <workspace> <toolkit> <lib>/<staging>
#         the workspace's pinned sources and the generation's build outputs, under the workspace's
#         build lock (`<workspace>/.lake/build.lock`, the one the lake shim takes for a build there)
#         and a shared hold of the machine's generations (none is pruned while it is linked from)
#     lean_workspace.sh seed <from workspace> <to workspace> <rel>…
#         each <rel> (under `.lake/build`) of one workspace placed in another, as `pin` places a
#         generation's: the linked kinds hard links, the rest copies (a promotion's workspace seeded
#         with its run's paper outputs; Lake in it still judges them by their traces)
#     lean_workspace.sh linked <file name>
#         exit 0 when a file of that name is hard-linked into a workspace, 1 when it is copied (tests)
#
# Hard links, and why they are safe. A workspace's build outputs are hard links to the generation's
# files on the same local disk: a rebuild in the workspace never writes the shared inode, because
# Lake (4.33: `Module.clearOutputArtifacts`, `buildArtifactUnlessUpToDate`'s `doBuild`, and
# `compileStaticLib`) unlinks every output it is about to make before making it. What Lake writes
# IN PLACE (`IO.FS.writeFile`, `Handle.mk .write`: the `.trace` and `.hash` files, `.rsp`,
# `.trace.nobuild`) is copied, not linked. Only the kinds `linked` names are linked (every other file
# is copied), and the generation's linked files are made read-only: an in-place write that Lake
# would ever attempt fails loudly instead of changing every workspace's copy.
#
# Never carried (2026-11-11): `ir/<module>.setup.json` — neither packed, nor pinned, nor seeded.
# Lake writes it just before it compiles the module, for that compile alone (`lean --setup`, then
# `leanir`: Lake/Build/Actions.lean `compileLeanModule`); nothing reads it after: whether a module is
# up to date is its trace's verdict, and a rebuild writes it anew (checked on a copy of a workspace
# with every one deleted: `lake build --no-build` up to date; an edited module and its dependents
# rebuilt, each one's written again). About 1.5 MB a module — 60% of a generation, and copied
# into every workspace.
set -euo pipefail
shopt -s nullglob

die() { echo "lean_workspace: $*" >&2; exit 1; }
[[ $# -ge 1 ]] || die "usage: $0 pack|unpack|pin|linked …"
cmd=$1; shift

# What is hard-linked: the compiler's outputs (made anew, never rewritten), Lean sources (never
# written by Lake), and the executables in `bin/` (no dot in the name).
linked() { # <path>
  local n=${1##*/}
  case $n in
    *.olean|*.olean.server|*.olean.private|*.ilean|*.ir|*.ir.sig|*.c|*.bc|*.ltar|*.o|*.export|*.noexport|*.a|*.so|*.lean) return 0 ;;
  esac
  [[ $1 == */bin/* && $n != *.* ]]
}
# The `find` test of the same set (keep in step with `linked`).
LINKED=( \( -name '*.olean' -o -name '*.olean.server' -o -name '*.olean.private' -o -name '*.ilean' -o -name '*.ir' -o -name '*.ir.sig'
  -o -name '*.c' -o -name '*.bc' -o -name '*.ltar' -o -name '*.o' -o -name '*.export' -o -name '*.noexport' -o -name '*.a' -o -name '*.so'
  -o -name '*.lean' -o \( -path '*/bin/*' ! -name '*.*' \) \) )
# What is never carried (the header): a file of this name is not packed, pinned or seeded.
dropped() { [[ $1 == *.setup.json ]]; }
DROPPED='*.setup.json'

# <src> placed at <dst>: a directory as a tree of hard links with the copied kinds copied, a file
# linked or copied; then renamed onto <dst> (a directory: the old one renamed away first).
place() { # <src> <dst>
  local src=$1 dst=$2 tmp old
  if [[ ! -d $src ]] && dropped "$src"; then return 0; fi
  tmp="$(dirname "$dst")/.pf-new.$(basename "$dst")"
  old="$(dirname "$dst")/.pf-old.$(basename "$dst")"
  rm -rf "$tmp" "$old"
  if [[ -d $src ]]; then
    cp -al "$src" "$tmp"
    # what is never carried: gone (the links only: the source keeps its files)
    find "$tmp" -type f -name "$DROPPED" -delete
    # the copied kinds: own files, not links (tar unlinks the link before it writes)
    (cd "$src" && find . -type f ! "${LINKED[@]}" ! -name "$DROPPED" -print0 | tar -c --null --no-recursion -T - -f -) | (cd "$tmp" && tar -x --unlink-first -f -)
  elif linked "$src"; then
    ln "$src" "$tmp"
  else
    cp -p "$src" "$tmp"
  fi
  # (2026-11-11) the staged link is the very file it replaces (a file pinned already, or a link of
  # the generation's): `mv` refuses one onto itself, and there is nothing to place
  if [[ ! -d $tmp && $tmp -ef $dst ]]; then rm -f "$tmp"; return 0; fi
  if [[ -d $dst && ! -L $dst ]]; then
    mv -T "$dst" "$old" && mv -T "$tmp" "$dst" && rm -rf "$old"
  else
    # (a directory is not renamed onto a link: an entry the workspace linked before it was pinned)
    if [[ -d $tmp && -L $dst ]]; then rm -f "$dst"; fi
    mv -fT "$tmp" "$dst"
  fi
}

# (2026-11-11) A generation unpacked shares the previous one's files that it has unchanged: each linked
# kind of the same path, size and bytes (`cmp`; a `.hash` sidecar that differs rules one out unread) is
# made a hard link to the previous generation's (read-only, as its own). Without it each generation
# had inodes of its own, and a workspace pinned to an older one held its sole copy once that was
# pruned (the 3 exes alone, 0.69 GB a generation). Under the generations' lock: nothing prunes the
# previous one meanwhile.
dedupe() { # <unpacked tmp dir> <gens dir> <its generation>
  local tmp=$1 gens=$2 n=$3 prev line s f old new a b
  prev=$({ ls -1 "$gens" | grep -E '^[0-9]+$' || true; } | sort -n | awk -v n="$n" '$1 < n' | tail -n 1)
  [[ -n $prev && -f $gens/$prev/.pf-complete ]] || return 0
  local -A size=()
  while IFS= read -r -d '' line; do size[${line#* }]=${line%% *}; done < <(cd "$gens/$prev" && find . -type f "${LINKED[@]}" -printf '%s %p\0')
  while IFS= read -r -d '' line; do
    s=${line%% *} f=${line#* }
    [[ ${size[$f]-} == "$s" ]] || continue
    old=$gens/$prev/$f new=$tmp/$f
    if [[ -f $old.hash && -f $new.hash ]]; then
      a='' b=''
      IFS= read -r a < "$old.hash" || true
      IFS= read -r b < "$new.hash" || true
      [[ $a == "$b" ]] || continue
    fi
    cmp -s "$old" "$new" || continue
    ln -f "$old" "$new"
  done < <(cd "$tmp" && find . -type f "${LINKED[@]}" -printf '%s %p\0')
}

case $cmd in
  linked)
    linked "$1"
    ;;
  seed)
    [[ $# -ge 2 ]] || die "seed <from workspace> <to workspace> <rel>…"
    from=$1 to=$2; shift 2
    for rel in "$@"; do
      [[ -e $from/.lake/build/$rel ]] || continue
      mkdir -p "$(dirname "$to/.lake/build/$rel")"
      # (a file seeded before is a link to the same inode: `mv` refuses one onto itself)
      if [[ -f $to/.lake/build/$rel && ! -d $to/.lake/build/$rel ]]; then rm -f "$to/.lake/build/$rel"; fi
      place "$from/.lake/build/$rel" "$to/.lake/build/$rel"
    done
    ;;
  pack)
    [[ $# -eq 5 ]] || die "pack <toolkit> <out.tar.zst> <lib> <papers lib> <staging>"
    toolkit=$1 out=$2 lib=$3 papers=$4 staging=$5
    cd "$toolkit"
    src=() build=()
    for f in *.lean; do [[ $f == "$papers.lean" ]] || src+=("$f"); done
    for f in "$lib" lakefile.toml lake-manifest.json lean-toolchain; do [[ -e $f ]] && src+=("$f"); done
    for f in "${src[@]}"; do
      [[ $f == *.lean ]] || continue
      m=${f%.lean}
      for p in .lake/build/lib/lean/"$m" .lake/build/lib/lean/"$m".* .lake/build/ir/"$m" .lake/build/ir/"$m".*; do
        [[ -e $p ]] && build+=("$p")
      done
    done
    [[ -d .lake/build/bin ]] && build+=(.lake/build/bin)
    [[ ${#build[@]} -gt 0 ]] || die "$toolkit has no build outputs to pack"
    mkdir -p "$(dirname "$out")"
    tmp="$out.tmp.$$"
    trap 'rm -f "$tmp"' EXIT
    # (unanchored: `<lib>/<staging>` is left out of the sources and of both build trees; links followed)
    tar -c -h --exclude="$lib/$staging" --exclude='.nfs*' --exclude='*.nobuild' --exclude='.pf-*' --exclude="$DROPPED" -f - "${src[@]}" "${build[@]}" \
      | zstd -q -1 -T0 -f -o "$tmp"
    mv -f "$tmp" "$out"
    trap - EXIT
    ;;
  unpack)
    [[ $# -eq 2 ]] || die "unpack <archive> <node gen dir>"
    archive=$1 gen=$2 gens=$(dirname "$2")
    mkdir -p "$gens"
    (
      flock -w 1800 9 || die "timed out waiting for another unpack in $gens"
      if [[ ! -f $gen/.pf-complete ]]; then
        [[ -f $archive ]] || die "no generation archive $archive"
        tmp="$gen.tmp.$$"
        rm -rf "$tmp" "$gen"
        mkdir -p "$tmp"
        zstd -q -dc "$archive" | tar -x -C "$tmp" -f -
        # the linked kinds are read-only: an in-place write of one fails instead of reaching every workspace
        find "$tmp" -type f "${LINKED[@]}" -exec chmod a-w {} +
        dedupe "$tmp" "$gens" "$(basename "$gen")"
        touch "$tmp/.pf-complete"
        mv -T "$tmp" "$gen"
      fi
      # the newest 3 generations stay (and this one); a workspace keeps its own links to older ones
      keep=$(basename "$gen")
      { ls -1 "$gens" | grep -E '^[0-9]+$' || true; } | sort -n | head -n -3 | while read -r n; do
        [[ $n == "$keep" ]] || rm -rf "${gens:?}/$n"
      done
      find "$gens" -maxdepth 1 -name '*.tmp.*' -mmin +60 -exec rm -rf {} + 2>/dev/null || true
    ) 9> "$gens/.lock"
    ;;
  pin)
    [[ $# -eq 4 ]] || die "pin <node gen dir> <workspace> <toolkit> <lib>/<staging>"
    gen=$1 ws=$2 toolkit=$3 staging=$4
    mkdir -p "$ws/.lake/build"
    (
      # the generation stays while it is linked from (an unpack prunes under the lock exclusive)
      flock -s -w 1800 8 || die "timed out waiting for an unpack in $(dirname "$gen")"
      [[ -f $gen/.pf-complete ]] || die "generation $gen is not unpacked"
      # (a short wait: the run keeps the generation it has, and re-pins at its next safe point)
      flock -w 120 9 || die "the builds in $ws held its lock for 2 min: not re-pinned"
      for e in $(ls -A "$gen"); do
        case $e in .lake|.pf-*) continue ;; esac
        place "$gen/$e" "$ws/$e"
      done
      # the staging tree is no part of a generation: the shared one, as a paper sees it
      if [[ -e $toolkit/$staging && -d $ws/${staging%%/*} && ! -e $ws/$staging ]]; then ln -s "$toolkit/$staging" "$ws/$staging"; fi
      for sub in lib/lean ir bin; do
        [[ -d $gen/.lake/build/$sub ]] || continue
        mkdir -p "$ws/.lake/build/$sub"
        for e in $(ls -A "$gen/.lake/build/$sub"); do place "$gen/.lake/build/$sub/$e" "$ws/.lake/build/$sub/$e"; done
      done
    ) 8> "$(dirname "$gen")/.lock" 9> "$ws/.lake/build.lock"
    ;;
  *) die "unknown command $cmd" ;;
esac
