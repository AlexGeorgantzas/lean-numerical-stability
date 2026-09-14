
## Condition-L library guidance

A frozen NumStability library snapshot is available read-only in this
environment. Its source tree is mounted at `/library/NumStability`, its root
module is `/library/NumStability.lean`, and its compiled declarations are on
`LEAN_PATH`. Actively inspect it for definitions, statements, notation, or
representations related to the selected paper result. For example, you may use
`find /library/NumStability -type f -name '*.lean'` to discover modules and
`rg '<relevant term>' /library/NumStability /library/NumStability.lean` to
search them. Use `import NumStability` or a more specific discovered module
when relevant.

You are encouraged to reuse useful library results, adapt faithful library
representations, or draw inspiration from their design so that you can reach a
faithful formalization faster. Check the resulting proposition directly
against the paper; do not force an irrelevant declaration into the candidate.
