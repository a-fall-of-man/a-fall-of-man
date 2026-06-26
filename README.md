# ACL2 Formal Systems Lab

A holistic repository containing:

- executable ACL2 books developed in dialogue with ACL2's automatic theorem prover;
- certification evidence and revision provenance;
- a reproducible GNU CLISP → self-hosted SBCL → ACL2 8.7 recovery stack;
- scripts and checksums for restoring and recertifying the environment.

No `skip-proofs`, `defaxiom`, trust tags, raw Lisp, program-mode escape, or equivalent soundness shortcuts are used in the release books.

## Layout

- `books/` — release ACL2 books.
- `evidence/` — certification transcripts and certificate provenance.
- `patches/` — focused historical diffs.
- `scripts/` — book certification helpers.
- `recovery/` — restore/repack scripts, build logs, provenance, and checksums.
- `docs/` — revision and community-book reading notes.

## Current books

| Book | Theme | Status |
|---|---|---|
| `zze-exotic-fertile-kernel.lisp` | Affine cocycles, word summaries, RLE, ropes, zippers, reversibility | Certified under ACL2 8.7; reproduced local run counted 6,308,931 prover steps |
| `zyl-verified-patch-calculus.lisp` | Verified edit scripts, normalization, compressed insertions, semantic summaries | Certified under ACL2 8.7; 941,554 prover steps |
| `zxh-cyclic-canon-calculus.lisp` | Cyclic rhythms, dihedral normalization, exact-cover canons, search, torus products | Canonical release name awaiting fresh basename-specific certification; preceding `zxz` candidate certified with 122,028 prover steps |

## Revision convention

The first two letters identify a book family. The third letter descends once per candidate actually loaded into ACL2: `z`, `y`, `x`, and so on. The successful release keeps the suffix reached by that proof-development history.

## Restore the toolchain

The recorded bootstrap chain is:

```text
GCC → GNU CLISP 2.49.95+ → SBCL 2.6.5 → self-hosted SBCL 2.6.5 → ACL2 8.7
```

See `recovery/docs/FORMAL_TOOLCHAIN_RECOVERY_README.md` and run:

```sh
sh recovery/scripts/RECOVER_FORMAL_TOOLCHAIN.sh
```

The prebuilt Linux x86-64 recovery archive is 75 MB. This repository records its exact checksum and reconstruction scripts; the archive itself must be added as a GitHub Release asset or pushed by native Git because the ChatGPT GitHub connector cannot stream local binary files. Source archives are identified by checksums and are not duplicated here.

ACL2 upstream: <https://github.com/acl2/acl2>
