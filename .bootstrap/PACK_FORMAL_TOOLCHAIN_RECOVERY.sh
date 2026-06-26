#!/bin/sh
set -eu
ROOT=/mnt/data
OUT=${1:-$ROOT/formal-toolchain-binary-recovery-v2.tar.zst}
shift || true

required="
clisp-install
sbcl-native-install
acl2-8.7-recovery/sbcl-saved_acl2
acl2-8.7-recovery/sbcl-saved_acl2.core
formal-toolchain-recovery-metadata
FORMAL_TOOLCHAIN_RECOVERY_README.md
RECOVER_FORMAL_TOOLCHAIN.sh
PACK_FORMAL_TOOLCHAIN_RECOVERY.sh
"

for p in $required; do
  [ -e "$ROOT/$p" ] || { echo "Missing $ROOT/$p" >&2; exit 1; }
done

# Additional arguments are interpreted as paths relative to /mnt/data and are
# included verbatim, making later bundle revisions easy to extend.
cd "$ROOT"
tar -I 'zstd -T1 -8' -cf "$OUT" $required "$@"
sha256sum "$OUT" > "$OUT.sha256"
echo "$OUT"
