# ACL2 / SBCL / GNU CLISP Binary Recovery Bundle

This bundle preserves the working binary stack built in this environment:

1. GNU CLISP 2.49.95+ installed under `/mnt/data/clisp-install`
2. self-hosted SBCL 2.6.5 installed under `/mnt/data/sbcl-native-install`
3. ACL2 8.7 launcher and core under `/mnt/data/acl2-8.7-recovery`

The ACL2 source tree is intentionally not duplicated in the binary bundle. If
`/mnt/data/acl2-8.7.tar.gz` is present, the recovery script restores the source
tree before overlaying the saved ACL2 launcher and core. Without the source
tarball, the saved ACL2 image can still start, but system-book work and full
source-level rebuilding are not available.

The payload is Linux x86-64 specific and assumes a sufficiently compatible
GNU/Linux userspace. The installed CLISP and the ACL2 launcher contain the
`/mnt/data` prefix, so restoration should use that path.

## Restore

Place these files in `/mnt/data`:

- `formal-toolchain-binary-recovery-v2.tar.zst`
- `RECOVER_FORMAL_TOOLCHAIN.sh`
- optionally `acl2-8.7.tar.gz`

Then run:

```sh
sh /mnt/data/RECOVER_FORMAL_TOOLCHAIN.sh
```

The script is non-destructive: it overlays the saved binary payload and does
not remove an existing ACL2 source tree or community-book certificate cache.

## Included evidence

The archive includes build/install logs, smoke-test output, and the provenance
manifest. `formal-toolchain-recovery-metadata/extras/` is reserved for related
artifacts that may be added in later bundle revisions.
