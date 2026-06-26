#!/bin/sh
set -eu

ROOT=/mnt/data
BUNDLE="$ROOT/formal-toolchain-binary-recovery-v2.tar.zst"
ACL2_ARCHIVE="$ROOT/acl2-8.7.tar.gz"
ACL2_TREE="$ROOT/acl2-8.7-recovery"

if [ ! -f "$BUNDLE" ]; then
  echo "Missing recovery bundle: $BUNDLE" >&2
  exit 1
fi

# Restore the pristine ACL2 source tree only when it is absent.  Never delete
# an existing tree, since it may contain a valuable community-book cert cache.
if [ ! -f "$ACL2_TREE/acl2.lisp" ] && [ -f "$ACL2_ARCHIVE" ]; then
  tmp="$ROOT/.acl2-recovery-extract.$$"
  rm -rf "$tmp"
  mkdir -p "$tmp"
  tar -xzf "$ACL2_ARCHIVE" -C "$tmp"
  if [ ! -d "$tmp/acl2-8.7" ]; then
    echo "ACL2 archive did not contain acl2-8.7/" >&2
    rm -rf "$tmp"
    exit 1
  fi
  mkdir -p "$ACL2_TREE"
  cp -a "$tmp/acl2-8.7/." "$ACL2_TREE/"
  rm -rf "$tmp"
else
  mkdir -p "$ACL2_TREE"
fi

# Overlay the installed CLISP, installed SBCL, ACL2 launcher/core, and metadata.
tar --zstd -xf "$BUNDLE" -C "$ROOT"

# Smoke-test all three layers.
"$ROOT/clisp-install/bin/clisp" -q -norc \
  -x '(progn (format t "CLISP-RECOVERY=~A~%" (+ 19 23)) (ext:quit))'

"$ROOT/sbcl-native-install/bin/sbcl" --noinform --non-interactive \
  --eval '(format t "SBCL-RECOVERY=~A~%" (+ 13 29))'

"$ROOT/acl2-8.7-recovery/sbcl-saved_acl2" <<'ACL2EOF'
(value-triple (list :acl2-recovery (+ 14 28)))
(good-bye)
ACL2EOF
