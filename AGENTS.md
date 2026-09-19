# Development workflow

- Make regular commits at coherent green milestones. Commit completed, verified work instead of
  accumulating it across successive proof-development sessions.
- Run the relevant Lean builds and proof audits before committing. Reuse the cached Mathlib builds;
  do not rebuild Mathlib from source when a compatible cache is available.
- For changes involving `external/ctml`, commit the submodule first, then commit its updated pointer
  together with the corresponding cDOT changes.
- Use author `Codex <codex@openai.com>` for Codex's commits, unless the user requests otherwise.
- Preserve unrelated user edits and keep unfinished claims explicit in the documentation.
