#!/usr/bin/env bash
# Provenance check for vendor/alpo/lean.
#
# Re-downloads the 14 parts published at https://alpo.ge/lean.tar.gz.part01 ... part14,
# checks them against vendor/alpo/SHA256SUMS (the hashes recorded when the tree was vendored
# on 2026-11-20), refuses archives containing links or paths that leave the extraction
# directory, extracts into a temporary directory, and checks that vendor/alpo/lean is
# byte-identical to the archive (vendor/alpo/lean/.lake, a local build directory, excluded).
#
# Usage: bash vendor/alpo/tools/provenance.sh
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cd "$work"

echo "==> downloading 14 parts"
for i in $(seq -w 1 14); do
  curl -sSfL --retry 3 -o "lean.tar.gz.part$i" "https://alpo.ge/lean.tar.gz.part$i"
done

echo "==> checking hashes against SHA256SUMS"
if command -v sha256sum >/dev/null; then sha256sum -c "$here/SHA256SUMS"; else shasum -a 256 -c "$here/SHA256SUMS"; fi

cat lean.tar.gz.part* > lean.tar.gz
gzip -t lean.tar.gz

echo "==> checking archive entries (regular files and directories only, no escaping paths)"
types="$(tar -tzvf lean.tar.gz | cut -c1 | sort -u | tr -d '\n')"
case "$types" in
  -|-d|d-) ;;
  *) echo "unexpected entry types: $types"; exit 1 ;;
esac
if tar -tzf lean.tar.gz | grep -nE '^/|(^|/)\.\.(/|$)'; then
  echo "archive contains absolute or parent paths"; exit 1
fi

echo "==> extracting and comparing with vendor/alpo/lean"
mkdir extracted
tar -xzf lean.tar.gz -C extracted
diff -rq --exclude=.lake extracted/lean "$here/lean"
echo "provenance OK: vendor/alpo/lean is byte-identical to the published archive"
