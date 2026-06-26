# Locally Bootstrapped ACL2 Toolchain Provenance

Recorded: 2026-06-25 UTC
Architecture: x86-64 Linux
Purpose: preserve the exact locally bootstrapped route used to obtain a working ACL2 8.7 and begin full community-books certification.

## 1. Source archives supplied by the user

- `/mnt/data/clisp-master.tar.gz`
- `/mnt/data/sbcl-2.6.5-source.tar.bz2`
- `/mnt/data/acl2-8.7.tar.gz`

SHA-256 checksums are in `/mnt/data/formal-toolchain-source-sha256.txt`.

## 2. GNU CLISP bootstrap

Built GNU CLISP 2.49.95+ (snapshot dated 2024-11-03) from source with GCC.

Configure invocation, corrected during the 2026-06-25 recovery replay:

```sh
cd /mnt/data/clisp-src
./configure \
  --ignore-absence-of-libsigsegv \
  --prefix=/mnt/data/clisp-install \
  --without-ffcall \
  --without-readline \
  --without-dynamic-modules \
  /mnt/data/clisp-build
```

Because the container runs as root, the configure-provided `FORCE_UNSAFE_CONFIGURE=1` override was used.

Then:

```sh
cd /mnt/data/clisp-build
make
make check
make install
```

Installed executable:

```text
/mnt/data/clisp-install/bin/clisp
```

Observed version:

```text
GNU CLISP 2.49.95+ (2024-11-03)
```

Caveat: the core build and installation succeeded, but `make check` later failed in socket-status tests and that test process segfaulted. Earlier core, compiler, CLOS, encoding, and file tests had passed. This CLISP build lacks libsigsegv, libffcall, readline, and dynamic modules by construction.

Logs:

- `/mnt/data/clisp-configure.log`
- `/mnt/data/clisp-make.log`
- `/mnt/data/clisp-check.log`
- `/mnt/data/clisp-install.log`

## 3. First SBCL build, cross-hosted by CLISP

SBCL source version: 2.6.5.

The build log records:

```sh
./make.sh \
  --prefix=/mnt/data/sbcl-install \
  --xc-host='/mnt/data/clisp-install/bin/clisp -ansi -q -norc -on-error abort'
```

This CLISP-hosted cross-build completed successfully and produced a runnable SBCL. It emitted tolerated `FAILURE-P` warnings for some cross-compiled objects, which motivated a clean self-hosted rebuild.

Source/build tree:

```text
/mnt/data/sbcl-2.6.5-src
```

Cross-built runtime/core used for the next stage:

```text
/mnt/data/sbcl-2.6.5-src/src/runtime/sbcl
/mnt/data/sbcl-2.6.5-src/output/sbcl.core
```

Log:

```text
/mnt/data/sbcl-build-clisp.log
```

## 4. Clean self-hosted SBCL rebuild

A pristine second SBCL source tree was built using the CLISP-produced SBCL as the cross-compilation host.

The log records:

```sh
./make.sh \
  --prefix=/mnt/data/sbcl-native-install \
  --xc-host='/mnt/data/sbcl-2.6.5-src/src/runtime/sbcl --core /mnt/data/sbcl-2.6.5-src/output/sbcl.core --noinform --disable-debugger --no-sysinit --no-userinit'
```

Installed runtime:

```text
/mnt/data/sbcl-native-install/bin/sbcl
```

Installed core:

```text
/mnt/data/sbcl-native-install/lib/sbcl/sbcl.core
```

Observed version:

```text
SBCL 2.6.5-85913ede1
```

The self-hosted build completed both Genesis passes, warm initialization, and 20 contrib modules without the earlier CLISP-host `FAILURE-P` warnings. Smoke test result: 30.

Logs:

- `/mnt/data/sbcl-build-native.log`
- `/mnt/data/sbcl-native-install.log`
- `/mnt/data/sbcl-native-smoke.log`

## 5. Pristine ACL2 8.7 build under self-hosted SBCL

Pristine build tree:

```text
/mnt/data/acl2-8.7-sbcl-build/acl2-8.7
```

Host Lisp:

```text
/mnt/data/sbcl-native-install/bin/sbcl
```

The ACL2 GNUmakefile's documented SBCL build route was used, with the self-hosted SBCL as `LISP` and the `sbcl-` saved-image prefix. No ACL2 source patches were used in this successful build.

Resulting ACL2 image:

```text
/mnt/data/acl2-8.7-sbcl-build/acl2-8.7/sbcl-saved_acl2
```

Matching core:

```text
/mnt/data/acl2-8.7-sbcl-build/acl2-8.7/sbcl-saved_acl2.core
```

A real `certify-book` smoke test succeeded, producing a certificate and fasl.

Logs:

- `/mnt/data/acl2-sbcl-make.log`
- `/mnt/data/acl2-sbcl-smoke.log`

## 6. Community books certification

Books tree:

```text
/mnt/data/acl2-8.7-sbcl-build/acl2-8.7/books
```

Official non-Quicklisp full target:

```sh
cd /mnt/data/acl2-8.7-sbcl-build/acl2-8.7/books
make -j1 -k regression-everything \
  USE_QUICKLISP=0 \
  ACL2=/mnt/data/acl2-8.7-sbcl-build/acl2-8.7/sbcl-saved_acl2
```

The run originally began at `-j3`, but was deliberately restarted at `-j1` when three unusually large books consumed about 3.6 GiB of the 4 GiB RAM available and no swap was present. Existing certificates were retained, so the serial run resumes from the prior frontier.

Live log:

```text
/mnt/data/acl2-community-books-full.log
```

PID file:

```text
/mnt/data/acl2-community-books-full.pid
```

Feature-gated omissions such as Quicklisp-, ACL2(r)-, solver-, or host-specific books are expected and are not certification failures.

## 7. Certified project baseline

Previously certified user-facing kernel:

```text
zze-exotic-fertile-kernel.lisp
```

The next intended local use of this toolchain is to certify `zze` and then iteratively certify the `zy*` patch-calculus books without relying on remote human relay.


## 8. Recovery replay after VM directory recycle

The executable directories were lost while the three source archives and top-level logs survived. The complete chain was replayed successfully:

- GNU CLISP configured through the top-level `./configure` wrapper and installed at `/mnt/data/clisp-install`.
- CLISP-hosted SBCL completed in 51 minutes and passed a live evaluation smoke test.
- A pristine self-hosted SBCL rebuild completed in 2 minutes 50 seconds and installed at `/mnt/data/sbcl-native-install`.
- Pristine ACL2 8.7 rebuilt at `/mnt/data/acl2-8.7-recovery/sbcl-saved_acl2`.
- A fresh theorem-bearing smoke book certified with 211 prover steps, producing both `.cert` and `.fasl`.

A compact binary recovery bundle was created:

```text
/mnt/data/acl2-8.7-sbcl-binary-recovery.tar.zst
/mnt/data/RECOVER_ACL2_8_7_SBCL.sh
/mnt/data/acl2-8.7-recovery-checksums.sha256
```

The bundle contains the self-hosted SBCL installation and ACL2 saved image/core. The restore script combines it with the surviving ACL2 source archive, avoiding another CLISP-hosted SBCL rebuild.

## Upstream ACL2 source location

User-supplied upstream project location: <https://github.com/acl2/acl2>

This URL was recorded on 2026-06-26 for future recovery convenience. It was not live-verified in this sandbox because web access was unavailable; the present ACL2 8.7 recovery used the previously uploaded `acl2-8.7.tar.gz` archive.

## 9. Binary recovery bundle v2 with GNU CLISP

A second, versioned binary bundle was created to preserve the full installed
bootstrap stack rather than only native SBCL and the ACL2 saved image:

```text
/mnt/data/formal-toolchain-binary-recovery-v2.tar.zst
```

It contains:

- `/mnt/data/clisp-install`, including the actual CLISP `lisp.run` and
  `lispinit.mem` artifacts;
- `/mnt/data/sbcl-native-install`;
- the ACL2 8.7 launcher and saved core;
- build/install logs, compatibility information, and payload checksums;
- non-destructive restore and repack scripts.

The ACL2 source archive remains external to keep the binary bundle compact.
When `/mnt/data/acl2-8.7.tar.gz` is available, the restore script reconstructs
the source tree before overlaying the saved ACL2 image. The bundle is Linux
x86-64 specific and assumes restoration under `/mnt/data`.
