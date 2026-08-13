# R12 private closure

The frozen B0004 private-closure TSV and private-normalization TSV are both
header-only. R12 therefore relocates 34 public declarations and zero private
declarations, has a header-only reverse closure, and performs no private-name
remangling.

PRIVATE_CLOSURE.tsv is byte-identical to the active-control artifact. The static
auditor also verifies the exact header-only private-normalization artifact
directly from active-control commit 5e075b947a63e84c784afecd00e1f130e21ea659.
