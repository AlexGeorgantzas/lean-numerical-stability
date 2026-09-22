# GPT-6 Sol admission gate — not passed

Before any measured task, an off-benchmark, read-only Titan Codex CLI probe
requested `gpt-6-sol` with `model_reasoning_effort=xhigh` and the existing
ChatGPT-account authentication. The installed CLI was `codex-cli 0.154.0`.
The provider returned HTTP 400 `invalid_request_error`:

> The 'gpt-6-sol' model is not supported when using Codex with a ChatGPT account.

The CLI also warned that model metadata for `gpt-6-sol` was not found locally.
The provider rejection, not the metadata warning alone, is the admission
blocker. The probe was ephemeral, used no benchmark PDF or task, and was not
charged to either condition. No measured Pilot-18 task has started.

Official OpenAI model documentation lists `gpt-6-sol` and `xhigh` for the API,
but it does not establish that this Titan ChatGPT account can use that model
through Codex CLI. Titan has no `OPENAI_API_KEY` environment variable. Do not
substitute another model, use another account or billing route, or fall back to
5.6 Sol inside a measured pilot without an explicit user decision and a new
frozen model identity.

Source: https://developers.openai.com/api/docs/models
