# llm-acl2-books: 90-book generated rational WFTA checkpoint

Release date: 2026-06-29

This archive is a source release of 90 ordinary ACL2 books. It retains the
84-book recovery, universal Rader/Toom--Cook compiler, rational Runge--Kutta
enclosure kernel, rational not-a-knot spline kernel, and repaired polynomial
sign bisection. It adds six tightly connected books that construct and certify
rational stereographic twiddle tables and compose them with the generated
WFTA compiler.

No ACL2(r), nonstandard analysis, real-number completion, or Lisp complex
number representation is used. Complex quantities are pairs of ACL2
rationals, and every new constructor and bound is finite and executable.

## New advanced chain

- `zci-stereographic-power-polynomials.lisp` generates exact coefficient
  recurrences for powers of `(1-t^2)+2ti` and proves evaluation equals repeated
  rational-pair multiplication.
- `zcj-generated-stereographic-certificate.lisp` computes the proper-power
  table and proves that half its exact minimum L1 distance from one is a strict
  orbit-separation certificate.
- `zck-stereographic-polynomial-closure.lisp` proves that normalization by
  `(1+t^2)^n` is the actual rational unit orbit and reduces closure to two
  rational polynomial residuals.
- `zcl-rational-polynomial-secant-bound.lisp` proves an executable
  coefficient/Horner bound on polynomial variation across a rational bracket.
- `zcm-bisected-stereographic-twiddle.lisp` converts a certified rational sign
  bracket and a finite bisection depth into a rational twiddle-system
  certificate with explicit closure and separation bounds.
- `zcn-bisected-generated-rational-wfta.lisp` composes that twiddle constructor
  with the universal primitive-root Rader/Toom--Cook compiler and proves the
  generated rational WFTA equals the direct rational DFT over the generated
  table.

## Fresh certification

The exact 90 `.lisp` files were copied into an empty workspace and certified
serially under ACL2 8.7 and SBCL 2.6.5. A second pass rebuilt zero books.
Complete `.cert.out` transcripts and all source/certificate hashes are under
`release-metadata/`. Implementation-specific `.cert`, `.fasl`, and `.port`
products are represented by hashes rather than included.

To re-certify after extraction:

```sh
export ACL2=/path/to/saved_acl2
export ACL2_SYSTEM_BOOKS=/path/to/acl2/books
/path/to/acl2/books/build/cert.pl -j1 *.lisp
```

`-j1` is recommended on memory-constrained machines.

## Remaining frontier

The end-to-end theorem consumes a finite bisection certificate. The next main
problem is to generate an initial rational sign bracket uniformly, preferably
through a certified finite root-isolation or signed-grid search layer, and to
integrate finite primitive-root search so fewer witnesses remain external.
