# llm-acl2-books: 82-book universal WFTA checkpoint

Release date: 2026-06-29

This archive is a source release of 82 ordinary ACL2 books.  It contains the
freshly recovered and extended 80-book line, a finite-residue permutation
prelude, and the universal theorem that derives the complete compact Rader
bank from the Rader index certificate and closes the generated
Rader/Toom--Cook WFTA compiler.

The release was built with ACL2 8.7 under the recovered SBCL image and the
verified basic community-books cache.  It contains no ACL2(r) books,
nonstandard analysis, real-number semantics, or Lisp complex-number
assumptions.  Complex quantities are rational pairs.

## Fresh certification result

The exact 82 `.lisp` files in this archive were copied to an empty workspace
and certified serially with:

```sh
export ACL2=/mnt/data/acl2-8.7-recovery/sbcl-saved_acl2
export ACL2_SYSTEM_BOOKS=/mnt/data/acl2-8.7-recovery/books
export ACL2_CUSTOMIZATION=NONE
/mnt/data/acl2-8.7-recovery/books/build/cert.pl -j1 *.lisp
```

The complete cold-run and idempotence logs, source/certificate hashes, source
diff, and trust audit are under `release-metadata/`.  Complete `.cert.out`
transcripts are retained.  Implementation-specific `.cert`, `.fasl`, and
`.port` products are represented by hashes rather than vendored.

## New certified WFTA closure

### `zcf0-finite-residue-permutation.lisp`

This small prelude proves the finite-list combinatorics needed before the
large Toom--Cook rewrite theory is imported: full positive-residue membership,
cardinality, duplicate-free position/nth inverses, and residue bounds for
permutations.

### `zcf-rader-index-implies-compact.lisp`

This book proves the missing semantic bridge:

```lisp
(implies (rgi-index-certificatep p inputs kernels outputs)
         (rgi-compact-bankp p outputs inputs kernels))
```

The proof first derives every compact Fourier matrix entry from the Rader
relation certificate, folds those pointwise equalities through the executable
row/output checkers, and then walks the output suffix to certify the whole
bank.

Consequently, a primitive-root orbit satisfying the already-certified finite
field order hypotheses automatically supplies both the generated Rader index
certificate and compact bank.  Composed with the universal generated
Toom--Cook certificate, ACL2 proves an end-to-end
`rwd-compiled-certifiesp` theorem and executable equality with the direct
rational DFT outputs for arbitrary prime order covered by those hypotheses.
No prime-specific relation table or separately supplied compact-bank
certificate remains in the theorem.

## Earlier checkpoint additions

`zcd-rational-runge-kutta-kernel.lisp` remains the small purely rational RK
enclosure hinge.  `zce-universal-rader-toom-cook-composition.lisp` remains the
generic composition theorem now discharged automatically by `zcf`.

## Next mathematical seam

The combinatorial WFTA compiler is now closed.  The next substantial target is
an executable, epsilon-driven rational generator for the twiddle seed
certificate used by `zbb-rational-cyclic-twiddle-system.lisp`: construct a
rational stereographic parameter whose power orbit closes within a requested
rational epsilon while its proper prefix remains rationally separated from
one.  This is a finite rational algebra and root-isolation problem, not an
appeal to real limits.

## Verification

From the extracted `llm-acl2-books` directory:

```sh
sha256sum -c SHA256SUMS
```

Then run the certification command above.  Use `-j1` in memory-constrained
environments.
