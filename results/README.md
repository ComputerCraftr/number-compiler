# Local research and validation outputs

Generated test logs, JUnit XML, JSON measurements, guard reports, profiles,
databases and other run payloads are ignored here. They belong in local run
directories or CI artifact storage, not in Git. The September 11 cleanup removed
these files from the working tree; it did not rewrite existing Git history.

Reviewed Markdown summaries and Python reproduction scripts remain versioned.
Historical summaries record what a particular run observed. Their raw artifact
paths describe local outputs and are not downloadable evidence in this checkout.
Historical fingerprints and reported passes do not certify a later source tree.

Generate fresh evidence with the canonical `devtools` commands or the retained
checkpoint drivers. Some comparison scripts need outputs from a preceding driver
or a separate baseline run. Use a fresh run directory and preserve it locally
while reviewing a result. Keep concise conclusions, commands, limitations and
source fingerprints in reviewed summaries; do not paste console transcripts.

This retention policy does not change release gates. Full release evidence must
still be generated and checked against the current source, using the existing
process guard and test-run evidence checks. A summary alone cannot satisfy those
checks. See [development guidance](../docs/development.md).

Fixtures and required kernel assets belong beside their source owners outside
this output directory. JSON and XML are not globally ignored: legitimate inputs
remain reviewable.
