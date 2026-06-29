# llm-acl2-books release note

Release date: 2026-06-29 NZST (2026-06-28 UTC)

This source release contains 78 ACL2 books. It integrates the original 62-book bundle with 16 new books proving universal generated Toom-Cook and Rader-index results, plus narrow integration changes to the existing length-66 and length-67 books.

## Certification status

The exact source tree in this archive was certified from a cold, source-only directory with ACL2 8.7 on SBCL 2.6.5, using the recovered ACL2 executable and the ACL2 8.7 community books:

```sh
export ACL2=/path/to/sbcl-saved_acl2
export ACL2_SYSTEM_BOOKS=/path/to/acl2-8.7/books
/path/to/acl2-8.7/books/build/cert.pl -j1 *.lisp
```

Result:

- 78 source books
- 78 matching `.cert` files produced
- serial certification exit status 0
- a second identical `cert.pl` pass reported that nothing remained to be done
- no `skip-proofs`, `defaxiom`, trust-tag, or raw-Lisp admission events occur in the source books
- three `:mode :program` declarations occur in two older report/file-I/O books (`zby-text-file-census.lisp` and `zez-self-checking-object-manifest.lisp`); these are executable I/O utilities, not theorem admissions

The `.cert`, `.fasl`, and `.port` products are deliberately not vendored in this source archive. They are implementation and installation artifacts. The included logs and SHA-256 manifest record the tested source release.

## New universal Toom-Cook books

- `zbn-rational-polynomial-root-bound.lisp`
- `zbo-rational-lagrange-interpolation.lisp`
- `zbp-rational-lagrange-reconstruction.lisp`
- `zbq-universal-toom-cook-certificate.lisp`
- `zbr-universal-toom-cook-moments.lisp`
- `zbs-universal-toom-cook-certificate.lisp`
- `zbt-universal-generated-compact.lisp`

These books replace a large concrete length-66 moment computation with general rational polynomial mathematics. ACL2 proves generated compact Toom-Cook certification, generated plan certification, and cyclic-convolution correctness for every positive length.

## New universal Rader-index books

- `zbu-rader-power-orbit.lisp`
- `zbv-rader-power-permutation.lisp`
- `zbw-rader-orbit-permutation.lisp`
- `zbx-rader-inverse-orbit.lisp`
- `zby-rader-index-relation.lisp`
- `zbz-rader-relation.lisp`
- `zca-universal-rader-relation.lisp`
- `zcb-universal-rader-certificate.lisp`
- `zcc-universal-generated-rader-certificate.lisp`

These books prove the generated Rader orbit and relation certificate from primality, nonzeroness, and multiplicative order. The prime-67 certificate is therefore a theorem instance rather than an evaluated 66-by-66 relation table.

## Revised integration books

- `zbe-generated-cyclic66.lisp` now imports the universal Toom-Cook proof locally and exports only the length-66 instance theorem. This keeps the downstream rewrite environment narrow.
- `zbl-generated-rader67.lisp` now derives the generated prime-67 index certificate from the universal Rader theorem.

The unfinished canonical rational-twiddle bisection development is intentionally absent. It is packaged separately in `llm-WIP.tar.gz` and is explicitly not certified.

## Verifying the archive

From the extracted directory:

```sh
sha256sum -c SHA256SUMS
```

Then run the certification command above. Use `-j1` in memory-constrained environments; several books are large enough that concurrent SBCL certification can exceed a 4 GiB limit.
