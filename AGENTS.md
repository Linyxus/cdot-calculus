# Development workflow

- Use parallel subagents for independent proof, implementation, and review tasks. Give each a
  bounded objective and disjoint file ownership, and exchange compact handoffs to avoid repeatedly
  reloading the whole development. Keep integration and final verification coordinated.
- For the DOT/CTML connection, read `notes/fcct-checkpoint.md` first and consult the longer status
  document selectively. Keep that checkpoint current when committing a research milestone.
- Preserve record-guarded recursion as a requirement of the DOT translation target. An experimental
  model's arrow-only guard is not a replacement for that requirement; adapt the model or encoding.
- Make regular commits at coherent green milestones. Commit completed, verified work instead of
  accumulating it across successive proof-development sessions.
- Run the relevant Lean builds and proof audits before committing. Reuse the cached Mathlib builds;
  do not rebuild Mathlib from source when a compatible cache is available.
- For changes involving `external/ctml`, commit the submodule first, then commit its updated pointer
  together with the corresponding cDOT changes.
- Use author `Codex <codex@openai.com>` for Codex's commits, unless the user requests otherwise.
- Preserve unrelated user edits and keep unfinished claims explicit in the documentation.
