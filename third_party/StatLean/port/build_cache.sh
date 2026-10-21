#!/usr/bin/env bash
# StatLean's compiled files (oleans), kept as a GitHub release asset so that a toolkit's first
# build of StatLean replays in about a minute instead of compiling 1,143 files (about 45 minutes on
# 32 cores). Lake trusts a cached file only when its recorded inputs match, so nothing stale is used.
#
#   port/build_cache.sh fetch     download the archive for this checkout's StatLean sources and
#                                 unpack it into third_party/StatLean/.lake/build
#   port/build_cache.sh pack      (maintainer) archive .lake/build after a full `lake build` here
#                                 and upload it; needs `gh` with write access
#
# The asset is statlean-build-<key>.tar.zst on the release tag `build-cache`; <key> is a hash of
# the tracked Lean sources and the pins (StatLean/, StatLean.lean, lakefile.toml, lean-toolchain,
# lake-manifest.json), so an archive is only ever offered to the sources it was built from.
set -euo pipefail
REPO="${STATLEAN_CACHE_REPO:-Jiyuan-Tan/PaperFormalizer}"
TAG="${STATLEAN_CACHE_TAG:-build-cache}"
HERE="$(cd "$(dirname "$0")/.." && pwd)"
cd "$HERE"

for tool in git tar zstd; do
  command -v "$tool" >/dev/null || { echo "build_cache: $tool is required" >&2; exit 1; }
done
if command -v sha256sum >/dev/null; then sha() { sha256sum | cut -d' ' -f1; }; else sha() { shasum -a 256 | cut -d' ' -f1; }; fi
key="$(git ls-tree -r HEAD StatLean StatLean.lean lakefile.toml lean-toolchain lake-manifest.json | sha | cut -c1-16)"
if [ -n "$(git status --porcelain -- StatLean StatLean.lean lakefile.toml lean-toolchain lake-manifest.json)" ]; then
  echo "build_cache: the StatLean sources here differ from the commit; no archive matches them" >&2; exit 1
fi
asset="statlean-build-$key.tar.zst"

case "${1:-}" in
  fetch)
    tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
    # The release asset is public: curl fetches it (gh is a fallback, e.g. for a private fork).
    if command -v curl >/dev/null && curl -fsSL --retry 3 -o "$tmp/$asset" "https://github.com/$REPO/releases/download/$TAG/$asset" 2>/dev/null; then :
    elif command -v gh >/dev/null && gh release download "$TAG" --repo "$REPO" --pattern "$asset" --dir "$tmp" 2>/dev/null; then :
    else
      echo "build_cache: no archive $asset on $REPO ($TAG), or it cannot be read (a private repository needs \`gh auth login\`). Lake will compile StatLean from source: once, and long." >&2
      exit 1
    fi
    mkdir -p .lake
    zstd -dc "$tmp/$asset" | tar -x -C .lake
    echo "build_cache: unpacked $(find .lake/build/lib -name '*.olean' | wc -l | tr -d ' ') oleans for sources $key into $HERE/.lake/build"
    ;;
  pack)
    command -v gh >/dev/null || { echo "build_cache: pack needs gh" >&2; exit 1; }
    [ -d .lake/build/lib ] || { echo "build_cache: nothing built here (.lake/build/lib): run \`lake build\` first" >&2; exit 1; }
    out="${TMPDIR:-/tmp}/$asset"
    tar -c -C .lake build | zstd -T0 -10 -q -o "$out" -f
    gh release view "$TAG" --repo "$REPO" >/dev/null 2>&1 \
      || gh release create "$TAG" --repo "$REPO" --title "Build cache" --notes "Compiled files of the adapted libraries, fetched by third_party/<Name>/port/build_cache.sh. Not a source release."
    gh release upload "$TAG" "$out" --repo "$REPO" --clobber
    echo "build_cache: uploaded $asset ($(du -h "$out" | cut -f1))"
    rm -f "$out"
    ;;
  *) sed -n '2,13p' "$0"; exit 2 ;;
esac
