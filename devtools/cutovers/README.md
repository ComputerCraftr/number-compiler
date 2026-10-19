# Pending comma global-future cutover

`comma-global-future.patch` is an unapplied, atomic review patch against the
current working sources. It replaces the finite public forest admission path
with the existing authenticated global-provider interface, removes the retired
forest code/data and audit registration, and migrates packaging, tests and
current documentation together. It does not register a release artifact.

The packaged JSON in the patch remains a candidate. Its integrity digest is not
proof authority. With the current empty release registry, applying this patch
would refuse public comma values and leave its positive release assertions red.

Activate only after the concrete B1, B32, global induction and producer/consumer
kernel gates pass under the central validation policy. Independently review the
artifact bytes, global claims, source binding and structural-termination bridge
before registering authority. Then check and apply the patch with Git and run
the existing guarded release runner, including the positive comma CLI and
installed-wheel gates. Do not treat fail-closed tests as positive acceptance.

The patch retires forest-verifier and finite-certificate memo tests with their
implementation. Independent literal seam comparisons remain; provider authority,
generation, malformed input, metadata laziness and later-fork tests protect the
replacement. Current API and resource-lifecycle fixes are retained in the rebase.
Developer-only trace audits retain explicit work bounds and reject exhaustion;
those bounds do not supply production fuel or prove termination outside an
admitted source domain.

This directory is authored source, rather than an ignored validation result.
Review the patch against the working tree before applying; later source edits
may require another rebase. No proof success is asserted by its presence.
