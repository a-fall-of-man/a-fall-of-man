# llm-acl2-books: recovered 80-book progress checkpoint

Release date: 2026-06-29

This archive is a source release of 80 ACL2 books: the recovered and freshly
re-certified 78-book line, plus one small purely rational Runge--Kutta kernel
and one universal Rader/Toom--Cook composition book.

It was built with ACL2 8.7 under the recovered SBCL image and the verified
basic community-books cache.  The release remains ordinary ACL2 throughout.
It contains no ACL2(r) books, real-number semantics, nonstandard analysis, or
complex Lisp-number dependency.

## Fresh certification result

The exact 80 `.lisp` files in this archive were copied to an empty
certification workspace and certified serially with:

```sh
export ACL2=/mnt/data/acl2-8.7-recovery/sbcl-saved_acl2
export ACL2_SYSTEM_BOOKS=/mnt/data/acl2-8.7-recovery/books
export ACL2_CUSTOMIZATION=NONE
/mnt/data/acl2-8.7-recovery/books/build/cert.pl -j1 *.lisp
```

Results:

- 80 source books;
- 80 fresh `.cert` files and 80 fresh `.cert.out` transcripts;
- cold serial certification exit status 0;
- second identical pass exit status 0 and rebuilt zero books;
- zero source differences between this release and the certified workspace;
- no `skip-proofs`, `defaxiom`, trust-tag, or raw-Lisp admission forms;
- three older `:mode :program` I/O declarations, listed in
  `release-metadata/TRUST-AUDIT.txt`, not used to admit logical theorems.

All 80 fresh certification transcripts are retained under
`release-metadata/fresh-certification-logs/`.  Generated `.cert`, `.fasl`, and
`.port` products are not vendored because they are toolchain/install products;
their fresh certificate hashes are recorded in
`release-metadata/FRESH-CERTIFICATE-SHA256SUMS`.

## New certified progress

### `zcd-rational-runge-kutta-kernel.lisp`

This deliberately small book defines exact rational weighted stage sums and a
rational Runge--Kutta update.  Its principal theorem proves a convex enclosure:
nonnegative rational weights summing to one, together with rational stage
slopes between `lo` and `hi`, force the nonnegative-step update between
`y + h*lo` and `y + h*hi`.

The theorem is finite, executable, and wholly rational.  It assumes no ODE
solution, derivative, integral, limit, completion of the rationals, or ACL2(r)
object.  Later books may attach algebraic or recurrence-generated stage
certificates without changing this kernel's trust boundary.

### `zce-universal-rader-toom-cook-composition.lisp`

This book composes the generated compact Toom--Cook convolution certificate
with finite Rader index and compact-bank certificates.  It proves:

- a reusable joint compact certificate;
- a general `rwd-compiled-certifiesp` theorem;
- executable equality between the compiled WFTA and direct rational DFT
  outputs; and
- a symbolic complex-product-count formula for generated Toom--Cook terms.

The next universal keystone is now exact rather than atmospheric: construct
the compact Rader bank from the generated primitive-root orbit and prove it
satisfies `rgi-compact-bankp`.  The new composition theorem will then remove
the final supplied compact-bank hypothesis from the arbitrary-prime compiler.

## Crash recovery result

The reset report said that `zam-qcx-adp-linear.lisp` and
`zaw-rational-cauchy-interest.lisp` had been lost, and that the reconstructed
`zax-rational-winograd-interface` had stopped before certification.  The
attached baseline contained later sources for all three.  ACL2 freshly
certified them and every dependent rational DFT, Winograd, ADP, Toom--Cook, and
Rader book.

The older failed reconstructed `zax` draft and the surviving Cauchy precursor
are preserved, explicitly as historical WIP, in the companion `llm-WIP`
archive.

## Mathematical content

The release includes generic algebraic dynamic programming, ranked shortest
paths, rational-pair DFT stability, arbitrary-length rational Fourier kernels,
proof-carrying bilinear convolution plans, shared-product Winograd banks,
general Rader/Winograd compilation, direct-equivalence and rational-only
interfaces, rational twiddle infrastructure, universal generated Toom--Cook
certificates, universal Rader-index certificates, the new universal
composition theorem, the rational RK enclosure kernel, and the independent
generic proof-engineering books from the original release.

The universal Toom--Cook books prove generated compact cyclic-convolution
certification for every positive size.  The universal Rader books derive the
generated orbit/relation certificate from finite-field order hypotheses, so
the prime-67 result is a theorem instance rather than a hardcoded relation
table.

## Verification

From the extracted `llm-acl2-books` directory:

```sh
sha256sum -c SHA256SUMS
```

Then run the certification command above.  Use `-j1` in memory-constrained
environments.
