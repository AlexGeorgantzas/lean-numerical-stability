# HighamBench T4 durable-artifact policy — v1

Persist and hash the exact versioned role prompts, source/Lean packets,
manifests, campaign plans, resumable checkpoints, validated final JSON role
outputs, provenance records, and semantic audit/repair ledgers. These durable
artifacts are the reusable workflow state for later papers and fresh sessions.

Do not make raw hidden reasoning, chain-of-thought, or unvalidated conversational
transcripts a workflow dependency. A fresh session must be able to resume from
the authenticated durable artifacts without replaying a prior chat.
