# llm-acl2-books: 99-book certified checkpoint

This portable archive contains 99 ordinary ACL2 source books and the complete
fresh `.cert.out` transcript for every source.  The sources were copied into an
empty workspace and certified serially under ACL2 8.7/SBCL 2.6.5.  A second
certification invocation rebuilt zero books.

The closing WFTA sequence is `zct` through `zcw`.  For odd prime transform
orders, `zcw-total-rational-wfta-correct` has no primitive-root witness, sign
bracket, search depth, bisection precision, resource fuel, twiddle table, Rader
index table, compact bank, or Toom-Cook plan among its hypotheses.  ACL2
constructs those objects and proves equality with the direct rational DFT over
the generated rational twiddle table.

Important specification boundary: the total explicit twiddle uses a very small
positive rational stereographic parameter.  It satisfies the project's unit,
approximate-closure, and strict proper-power-separation certificate, but as
epsilon shrinks it approaches 1 rather than selecting the conventional first
primitive-root sector.  The earlier certified sector-bracket/bisection books
remain in this archive as the stronger geometric construction.

No `.cert` binaries are included; those are Lisp-implementation-specific.
