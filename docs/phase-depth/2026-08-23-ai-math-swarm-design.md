# Governed AI mathematics swarm

The swarm is a campaign engine, not a truth engine. It fans each locked statement out to
independent roles—prover, refuter, generalizer, skeptic, and explainer—then stores every
candidate in an immutable, content-addressed evidence ledger. Only deterministic gates may
promote a result: statement preservation, source hygiene, Lean compilation, and an AXLE
axiom audit pinned to `lean-4.32.2`. Computations and explanations remain separate registers.

The important asymmetry is deliberate: agents can cheaply create and criticize candidates;
they cannot mark them proved. A theorem becomes publishable only after the repository's
existing three-leg chain agrees: local Lean, independent AXLE, and an axiom-clean attestation.

## Campaign loop

1. Lock exact declarations and prerequisites in a versioned program manifest.
2. Dispatch independent roles concurrently; preserve failures as evidence.
3. Run adversarial review and formal gates on every candidate.
4. Promote only gate-complete artifacts; never infer success from prose or provider status.
5. Generate a plain-language report linked to exact evidence hashes.
6. Unlock dependent targets only from verified task IDs.

The PhaseDepth manifest encodes nonabelian classification, the missing permutation-determinant
factorization, transfer determinant, Frobenius/Artin generalization, finite spectral RH, and a
preregistered discrimination experiment.

```bash
python3 -m swarm.cli program-check swarm/programs/phase_depth.json
python3 -m swarm.cli program-init swarm/programs/phase_depth.json --store .swarm
python3 -m swarm.cli evidence-audit --store .swarm
python3 -m unittest tests.test_swarm -v
```

External submission is intentionally not automatic. The Aristotle adapter requires an
explicit operator call and configured credentials, preventing planning commands from silently
spending quota or manufacturing registry claims.
