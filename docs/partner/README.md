# Partner materials

Partner-ready outputs from the Verified Intelligence program. **Regenerate counts** before external freeze:

```bash
python3 scripts/gen_program_report.py   # → docs/PROGRAM-REPORT.md
python3 -m pipeline.scripts.pipeline_cli ledger
```

Pin to a git commit hash when sharing PDFs.

| Doc | Audience | Purpose |
|-----|----------|---------|
| [2026-08-02-verified-intelligence-strategy-brief.md](./2026-08-02-verified-intelligence-strategy-brief.md) | IonQ, SAIR, AI Tinkerers | Strategy: formalize → verify → deploy |
| [torus-honesty-audit.md](./torus-honesty-audit.md) | Eng + partners | P0/P1 fixes so torus does not overclaim |
| [mathlib-physlean-harvest-plan.md](./mathlib-physlean-harvest-plan.md) | Eng / research | Verification at scale via Mathlib + PhysLean |
| [lean-physics-repo-harvest.md](./lean-physics-repo-harvest.md) | Fleet + research | Concrete repos + first-5 decls per folder |
| [claude-remarks-review-2026-08-02.md](./claude-remarks-review-2026-08-02.md) | Multi-agent collab | Review of Claude board/handoff/WIP |
| [quantumproof-formal-targets.md](./quantumproof-formal-targets.md) | QuantumProof / IonQ | Formal target inventory + first demo scope |

## Related repo surfaces

| Path | Role |
|------|------|
| [`docs/PROGRAM-REPORT.md`](../PROGRAM-REPORT.md) | Live registry snapshot (generated) |
| [`docs/SETTLE-FACTORY.md`](../SETTLE-FACTORY.md) | Certificate factory operator runbook |
| [`pipeline/`](../../pipeline/) | Multi-domain attack pipeline |
| [`observatory/`](../../observatory/) | Derived claim badges (local) |

## Brand sentence

> We ship what is proven and mark what is not.
