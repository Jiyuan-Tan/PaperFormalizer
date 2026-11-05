#!/usr/bin/env bash
# Keep a toolkit's Lean dependencies (each `.lake/packages/<package>`: Mathlib, Batteries, Aesop, … with
# their sources, git checkout and compiled libraries) and its Lean toolchain on each machine's local disk
# instead of a shared network file system.
#
#     lean_local_cache.sh pack   <toolkit> <local-root>   once: one archive per package and the toolchain
#     lean_local_cache.sh sync   <toolkit>                on each machine, before any Lean runs there
#     lean_local_cache.sh link   <toolkit>                once, on a synced machine: Lean uses the local copies
#     lean_local_cache.sh pack-toolchain <toolkit>        the Lean toolchain alone
#     lean_local_cache.sh toolchain-bin <toolkit>         this machine's copy of the toolchain, for PATH
#     lean_local_cache.sh status <toolkit>
#     lean_local_cache.sh undo   <toolkit>                back to the packages on the shared disk
#
# Why. Every Lean process that imports Mathlib maps all of its ~5,700 `.olean` files, and every `lake`
# call opens each dependency's git data, lakefile and sources to check them. On NFSv4 each mapped file
# is an open state the server tracks, and when the server revokes state the client re-tests every one
# (TEST_STATEID, thousands a second) while every other open on the mount waits — seconds per file. Read
# from local disk, Lean and Lake cost the network nothing for what never changes.
#
# How. `pack` writes each package as one archive (`.lake/packages/.pf-pkgs/<package>.tar`, stamp beside
# it), the toolchain as `.pf-toolchain.tar`, and `<local-root>` into `.pf-local-root`: a machine copies one
# file per package, not ~120,000 (opening a file is what is slow on a loaded mount). `sync` unpacks an
# archive into `<local-root>/pkgs/<package>` when the copy there is missing or of another stamp — into a
# new directory swapped in whole, under a lock, so a running Lean keeps the files it has mapped. `link`
# moves each package to `.pf-shared/<package>` (the master copy) and puts a symlink to the local copy in its
# place: the same path on every machine, so every machine that runs Lean must `sync` first — a cluster job
# script runs it before anything else, and stops when it fails. The toolchain is registered as the elan
# toolchain `pf-local`: a job uses the local copy by putting `toolchain-bin`'s output first on PATH and
# setting ELAN_TOOLCHAIN=pf-local; every other session keeps its own toolchain.
#
# Needs Linux with GNU tar, coreutils and util-linux (`flock`), and bash 4.
#
# What Lake writes into a package after `link` (its lakefile cache, a rebuild after a Mathlib update)
# lands in one machine's copy only: to update a dependency, `undo`, update, then `pack`, `sync`, `link`.
set -euo pipefail

die() { echo "lean_local_cache: $*" >&2; exit 1; }
[[ $# -ge 2 ]] || die "usage: $0 pack <toolkit> <local-root> | sync | link | pack-toolchain | toolchain-bin | status | undo <toolkit>"
cmd=$1
toolkit=$(cd "$2" && pwd) || die "no toolkit at $2"
packages="$toolkit/.lake/packages"
[[ -d $packages ]] || die "$toolkit has no .lake/packages (build it first)"
rootfile="$packages/.pf-local-root"
archives="$packages/.pf-pkgs"
shared="$packages/.pf-shared"
tcarchive="$packages/.pf-toolchain.tar"

root() { [[ -s $rootfile ]] || die "not packed: run pack first"; cat "$rootfile"; }
# the packages (names), from their directories or links — a link here with no copy behind it too (not this
# script's own .pf-* entries)
names() { for d in "$packages"/*; do [[ -d $d || -L $d ]] && echo "$(basename "$d")"; done; }
# where a package's files are on the shared disk: its directory, or its master copy once linked
master() { if [[ -L $packages/$1 ]]; then echo "$shared/$1"; else echo "$packages/$1"; fi; }
current() { [[ "$(cat "$1/.pf-stamp" 2>/dev/null)" == "$(cat "$2" 2>/dev/null)" ]]; } # <local copy> <its archive's stamp file>

toolchain_dir() {
  local spec; spec=$(tr -d '[:space:]' < "$toolkit/lean-toolchain") || die "no lean-toolchain in $toolkit"
  spec=${spec//\//--}; spec=${spec//:/---}
  echo "${ELAN_HOME:-$HOME/.elan}/toolchains/$spec"
}

pack_toolchain() { # <stamp>
  local tc; tc=$(toolchain_dir); [[ -x $tc/bin/lean ]] || die "no toolchain at $tc"
  tar -cf "$tcarchive.tmp" -C "$tc" . || die "packing the toolchain failed"
  mv "$tcarchive.tmp" "$tcarchive" && printf '%s\n' "$1" > "$tcarchive.stamp"
  echo "toolchain $(basename "$tc"): $(stat -c %s "$tcarchive") bytes packed"
}

unpack() { # <archive> <target>: the archive's contents at <target> when the copy there is of another stamp
  local archive=$1 target=$2 stamp
  [[ -f $archive ]] || return 0
  current "$target" "$archive.stamp" && return 0
  mkdir -p "$(dirname "$target")" || die "cannot create $(dirname "$target") on $(hostname)"
  (
    flock -w 3600 9 || die "timed out waiting for another sync of $target"
    current "$target" "$archive.stamp" && exit 0
    echo "lean_local_cache: unpacking $archive into $target on $(hostname)" >&2
    # (the stamp read before the archive: a pack that replaces both meanwhile leaves this copy older-stamped, so
    # the next sync takes the new one — never the old contents under the new stamp)
    stamp=$(cat "$archive.stamp") || die "no stamp beside $archive"
    rm -rf "$target.new" "$target.old"
    mkdir "$target.new" && tar -xf "$archive" -C "$target.new" || die "unpacking $archive failed"
    printf '%s\n' "$stamp" > "$target.new/.pf-stamp"
    # (a Lean running here keeps the files it mapped from the old copy)
    [[ -d $target ]] && mv "$target" "$target.old"
    mv "$target.new" "$target" && rm -rf "$target.old"
  ) 9> "$(dirname "$target")/.lock.$(basename "$target")"
}

case $cmd in
  pack)
    [[ $# -eq 3 ]] || die "pack needs <local-root>"
    [[ $3 == /* ]] || die "<local-root> must be absolute (the same path on every machine)"
    stamp="$(date -u +%Y%m%dT%H%M%SZ)-$$"
    mkdir -p "$archives"
    for p in $(names); do
      m=$(master "$p")
      # (an earlier version of this script linked only `.lake/build/lib`, its master at `lib.shared`:
      # that is what is packed as the package's lib)
      opts=()
      if [[ -L $m/.lake/build/lib && -d $m/.lake/build/lib.shared ]]; then
        opts=(--exclude=./.lake/build/lib --exclude='./.lake/build/lib.tar*' --transform='s#^\./\.lake/build/lib\.shared#./.lake/build/lib#')
      fi
      tar -cf "$archives/$p.tar.tmp" ${opts[@]+"${opts[@]}"} -C "$m" . || die "packing $p failed"
      mv "$archives/$p.tar.tmp" "$archives/$p.tar" && printf '%s\n' "$stamp" > "$archives/$p.tar.stamp"
      echo "$p: $(stat -c %s "$archives/$p.tar") bytes packed"
    done
    pack_toolchain "$stamp"
    printf '%s\n' "$3" > "$rootfile"
    ;;
  pack-toolchain)
    root >/dev/null
    pack_toolchain "$(date -u +%Y%m%dT%H%M%SZ)-$$"
    ;;
  sync)
    [[ -s $rootfile ]] || exit 0 # (a toolkit not packed: nothing to do)
    r=$(root)
    for a in "$archives"/*.tar; do [[ -f $a ]] && unpack "$a" "$r/pkgs/$(basename "$a" .tar)"; done
    unpack "$tcarchive" "$r/toolchain"
    ;;
  link)
    r=$(root)
    mkdir -p "$shared"
    for a in "$archives"/*.tar; do
      [[ -f $a ]] || continue
      p=$(basename "$a" .tar) target="$r/pkgs/$(basename "$a" .tar)"
      if [[ ! -L $packages/$p ]]; then
        current "$target" "$a.stamp" || die "$p is not synced on $(hostname): run sync here first"
        [[ -e $shared/$p ]] && die "$shared/$p exists but $packages/$p is not a link: resolve it by hand"
        # (a Lean running here keeps what it opened in the master copy: a rename moves no file)
        mv "$packages/$p" "$shared/$p" && ln -s "$target" "$packages/$p"
        echo "$p: -> $target"
      fi
      # the master copy as plain files again (an earlier version linked only its lib)
      b="$shared/$p/.lake/build"
      if [[ -L $b/lib && -d $b/lib.shared ]]; then rm "$b/lib" && mv "$b/lib.shared" "$b/lib" && rm -f "$b"/lib.tar "$b"/lib.tar.stamp "$b/lib/.pf-stamp"; fi
    done
    if [[ -f $tcarchive && ! -e ${ELAN_HOME:-$HOME/.elan}/toolchains/pf-local ]]; then
      current "$r/toolchain" "$tcarchive.stamp" || die "the toolchain is not synced on $(hostname): run sync here first"
      elan toolchain link pf-local "$r/toolchain" && echo "toolchain: elan pf-local -> $r/toolchain"
    fi
    ;;
  toolchain-bin)
    # the local toolchain's bin, for the front of PATH; nothing (exit 1) when this machine has no current copy
    r=$(root)
    current "$r/toolchain" "$tcarchive.stamp" && [[ -x $r/toolchain/bin/lake ]] || exit 1
    echo "$r/toolchain/bin"
    ;;
  status)
    r=$(cat "$rootfile" 2>/dev/null || true)
    for p in $(names); do
      where="shared disk"; [[ -L $packages/$p ]] && where="linked"
      here=""; [[ -n $r && -f $archives/$p.tar ]] && { current "$r/pkgs/$p" "$archives/$p.tar.stamp" && here=", current on $(hostname)" || here=", NOT synced on $(hostname)"; }
      echo "$p: $where$here"
    done
    if [[ -f $tcarchive ]]; then
      current "${r:-/nonexistent}/toolchain" "$tcarchive.stamp" && echo "toolchain: current on $(hostname)" || echo "toolchain: NOT synced on $(hostname)"
    fi
    ;;
  undo)
    for p in $(names); do
      [[ -L $packages/$p && -d $shared/$p ]] || continue
      rm "$packages/$p" && mv "$shared/$p" "$packages/$p"
      echo "$p: back on the shared disk"
    done
    # (a link left — its master copy missing — still needs the machines to sync: the root stays named)
    for p in $(names); do [[ -L $packages/$p ]] && die "$p is still a link with no master copy in $shared: resolve it by hand"; done
    rm -f "$rootfile"
    ;;
  *) die "unknown command $cmd" ;;
esac
