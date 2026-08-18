# Changelog — 2026-08-17 night hardening (honesty corrections)

Seven commits on `night/2026-08-17-math` (`ce03013..ee94165`) corrected the repo's stated
verification posture and hardened the gates that enforce it. This file exists so the corrected
posture is discoverable by doc readers, not buried in commit messages.

## Corrected verification posture (the headline)

The registry's `PROVED` entries are **AXLE-attested** (independent cloud kernel re-check at
lean-4.32.0, including axiom footprint, no-`native_decide`, and statement fidelity), but a **local
from-source `lake build` is pending for ALL 11,819 registry entries** — it has never run in this
repo. Every place that claimed or implied otherwise (README verification legs, observatory era
gallery + hero badge copy, two papers, the betrothed-numbers writeup) now says so explicitly.

## Commits

- **`ce03013`** — audit: truth-gate flags sorry-backed/unverified attestations as ERROR.
  `--strict` previously exited 0 on a sorry-backed module; now `module_verified != true`,
  per-declaration `sorryAx`, `axioms_ok: false`, or `axle_verdict "failed"` are ERROR. Effect on
  the live repo: 37 ERRORs, all confined to the stray unproven ConstellationSpectralFinal
  attestation — `--strict` is expected red until that attestation is resolved; do not weaken the
  gate to make CI green.
- **`b6e69b7`** — docs: honest verification posture. README's "triple verification" claim
  corrected: only the AXLE cloud re-check has run across the corpus; the local `lake build` leg is
  pending for every entry. Same fix in `observatory/era.html`.
- **`d114034`** — observatory: hero badge states AXLE-attested posture, not unqualified
  "machine-verified". Hero template fixed in `scripts/gen_observatory.py`; also regenerates
  `observatory/claims.json` + `claims.yaml` via `scripts/gen_observatory.py` (refreshing stale
  counts: PROVED 10,568 → 11,126, DEFINITION 581 → 626). `registry/theorems.json` itself remains
  uncommitted (human-gated).
- **`f7bdfd2`** — papers: verification claims aligned with actual registry/attestation posture.
  `brockian-fibonacci-anyon.tex`: only 4 of the 18 table theorems have attested registry
  counterparts; the other 14 are generator self-reports, now labeled as such.
  `brockian-verified-core.tex` similarly qualified.
- **`f4edfa8`** — writeup: betrothed-numbers note no longer claims a local lake build ran;
  verification lines now state AXLE cloud kernel attested, local lake build pending.
- **`abe47d7`** — audit: register-invariant re-derivation + full test coverage for the truth-gate.
  New `find_register_invariants` re-derives PROVED/CONDITIONAL/DISCHARGED invariants on
  `registry/theorems.json` entries themselves (previously only attestation files were inspected).
  + 17 tests in `tests/test_audit_registry_consistency.py`, wired into CI.
- **`ee94165`** — gen_registry: unambiguous `discharged_by` resolution (short-name collisions among
  11,126 PROVED entries could silently reclassify a CONDITIONAL as DISCHARGED; now requires
  fully-qualified or uniquely-resolving names — verified a no-op on the live corpus, summary
  unchanged at PROVED 11,126 / DISCHARGED 7) + fail-loud on malformed attestations (never skip —
  skipping silently shrinks the registry) + 10 new gating tests in `tests/test_gen_registry.py`
  (file now 22 tests; 39 total across both new/updated test files, all passing).

## Truth-gate status notes

- The 5 remaining WARNs are the pre-existing attestation-not-root-imported check
  (ConstellationComponentPaths, ConstellationSpectralFinal, GraphComponentGrouping,
  SieveSpectrumDeletion, SmallConnectedGraphSpectrum) — distinct from the new register-invariant
  check, which has zero findings on the live registry.
- Gate semantics spec: `docs/REGISTRY-CONSISTENCY.md` (updated 2026-08-18 to describe the
  truth-gate and register invariants).
