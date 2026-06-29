# llm-acl2-books: crash-recovery release

Release date: 2026-06-29

This archive is the recovered and freshly re-certified 78-book ACL2 source
release.  It was rebuilt after a container reset from the attached baseline,
the Winograd recovery snapshot, ACL2 8.7 source, the recovered SBCL image, and
the certified basic community-books cache.

## Fresh certification result

The exact 78 `.lisp` files in this archive were copied to an empty
certification workspace and certified serially with:

```sh
export ACL2=/mnt/data/acl2-8.7-recovery/sbcl-saved_acl2
export ACL2_SYSTEM_BOOKS=/mnt/data/acl2-8.7-recovery/books
export ACL2_CUSTOMIZATION=NONE
/mnt/data/acl2-8.7-recovery/books/build/cert.pl -j1 *.lisp
```

Results:

- 78 source books;
- 78 fresh `.cert` files and 78 fresh `.cert.out` transcripts;
- cold serial certification exit status 0;
- second identical pass exit status 0 and rebuilt zero books;
- zero source differences between this release and the certified workspace;
- no `skip-proofs`, `defaxiom`, trust-tag, or raw-Lisp admission forms;
- three older `:mode :program` I/O declarations, listed in
  `release-metadata/TRUST-AUDIT.txt`, not used to admit logical theorems.

All 78 fresh certification transcripts are retained under
`release-metadata/fresh-certification-logs/`.  Generated `.cert`, `.fasl`, and
`.port` products are not vendored because they are toolchain/install products;
their fresh certificate hashes are recorded in
`release-metadata/FRESH-CERTIFICATE-SHA256SUMS`.

## Crash recovery result

The reset report said that `zam-qcx-adp-linear.lisp` and
`zaw-rational-cauchy-interest.lisp` had been lost, and that the reconstructed
`zax-rational-winograd-interface` had stopped before certification.  The
attached baseline contained later sources for all three.  In this run ACL2
freshly certified:

- `zam-qcx-adp-linear.lisp`;
- `zaw-rational-cauchy-interest.lisp`;
- `zax-rational-winograd-interface.lisp`;
- every dependent rational DFT, Winograd, ADP, Toom-Cook, and Rader book.

The older failed reconstructed `zax` draft and the surviving Cauchy precursor
are preserved, explicitly as historical WIP, in the companion `llm-WIP`
archive.

## Mathematical content

The release includes generic algebraic dynamic programming, ranked shortest
paths, rational-pair DFT stability, arbitrary-length rational Fourier kernels,
proof-carrying bilinear convolution plans, shared-product Winograd banks,
general Rader/Winograd compilation, direct-equivalence and rational-only
interfaces, rational twiddle infrastructure, universal generated Toom-Cook
certificates, universal Rader-index certificates, and the independent generic
proof-engineering books from the original release.

The universal Toom-Cook books prove generated compact cyclic-convolution
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
