# llm-acl2-books: 107-book certified checkpoint

This portable archive contains 107 ordinary ACL2 source books and the complete
fresh `.cert.out` transcript for every source.  The sources were copied into an
empty workspace and certified serially under ACL2 8.7/SBCL 2.6.5.  A second
certification invocation rebuilt zero books.

The five new books form the first waterfall proof-plan vertical slice:

- finite compositional theory capsules;
- proof-action, feature-flow, cost, and receipt semantics;
- an ADP/min-plus optimizer with finite-graph global optimality;
- an untrusted `PROVE$` search shell that emits an ordinary checked `DEFTHM`;
- a replayable benchmark stable under unrelated theory extension.

In the cold benchmark, ACL2 rejects an empty theory after 40 steps and proves
the goal through a named two-rune semantic interface in 21 steps.  Repeating
the search after unrelated rewrite rules are enabled selects the same plan and
again takes 21 steps.

The complete rational-pair forward/inverse WFTA and state-stobj object I/O
books remain included unchanged.  See
`release-metadata/WATERFALL-PROOF-PLAN-VERTICAL-SLICE-2026-06-29.md` for the
new theorem boundary and next integration targets.

No `.cert` binaries are included; those are Lisp-implementation-specific.
