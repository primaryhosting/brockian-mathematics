# Settle Factory — Operator Runbook

> Certificate = unit of progress.  
> Stack: `attempt → prove/refute race → AXLE attest → no-theater lint → #print axioms → derived register → certificate (+ pipeline ledger)`.

**Commit:** `63e8e09` (`feat(settle): the certificate factory`).  
**Primary code:** [`scripts/settle.py`](../scripts/settle.py).  
**Do not** hand-assert `PROVED` — registers are derived.

---

## 1. What already exists

| Piece | Path | Role |
|-------|------|------|
| **Certificate factory** | `scripts/settle.py` | Closed loop: AXLE check + no-theater + axiom preview → `registry/certificates/<Module>.json` |
| **AXLE attest** | `scripts/attest.py` | Independent re-check; writes `registry/attestations/<Stem>.json` (committed SoT for registry) |
| **AXLE client** | `scripts/axle_client.py` | HTTP `check` / `verify_proof`; needs `AXLE_API_KEY` |
| **Register derivation** | `scripts/gen_registry.py` | `derive_register` + join attestations → `registry/theorems.json` + `REGISTRY.md` |
| **No-theater lint** | `scripts/no_theater_lint.py` | Blocks holes / theater patterns |
| **Command bridge** | `scripts/pipeline_attest_bridge.py` | **Print-only** exact `attest` / `gen_registry` / `settle` / pipeline commands (no network) |
| **Problem ledger** | `pipeline/core/ledger.py` + `pipeline_cli` | Problem-level registers incl. **REFUTED** / **PROVED** / **BLOCKED** |
| **SAIR Stage 2 card** | `pipeline/catalog/distillation/distill-etp-stage2.json` | Proof **or** counterexample certificate path |
| **SAIR tracker** | `pipeline/catalog/sair/sair-program-tracker.json` | Meta card; spawn children; no auto-submit |

**Certificates vs attestations**

| Artifact | Location | Git | Purpose |
|----------|----------|-----|---------|
| Attestation | `registry/attestations/*.json` | **Committed** | Source of truth for `gen_registry` |
| Certificate | `registry/certificates/*.json` | **Gitignored** (`.gitignore`) | Attempt/settle ledger; regenerable |
| Theorems | `registry/theorems.json` | Generated | Public theorem-level registers |
| Problem ledger | `pipeline/ledger/*` | Generated | Problem-level registers |

Example settled modules (already exercised): `FranklinFixedPoint` (VERIFIED, 34 PROVED + 1 DEFINITION), `CosTraceNorm` (VERIFIED, 25 PROVED).

---

## 2. Certificate as the unit of progress

A **certificate** is a machine-checked JSON record:

- `target` — Lean path settled  
- `prover` / `env` — e.g. `AXLE@lean-4.32.0`  
- `verdict` — see below  
- on success: `namespace`, `no_theater`, `axioms_clean`, `n_decls`, `registers`, per-decl rows  

**Verdicts** (`settle.py`):

| Verdict | Meaning | Exit |
|---------|---------|------|
| `VERIFIED` | Prove leg OK + no-theater + attestation rows | 0 |
| `REFUTED` | Refute module verified → original statement false | 0 |
| `FAILED` | Prove leg did not verify | 1 |
| `THEATER-BLOCKED` | no-theater lint failed | 1 |
| `BLOCKED` | **Dual-race:** prove **and** refute both verify (contradiction) | 1 |
| `ERROR` | Missing file / hard error | 1 |

Progress is “we have a certificate,” not “someone said it builds.”

---

## 3. Dual-race rule (prove ∧ refute)

```text
  prove-target.lean  ──AXLE──► prove_ok
  refute-target.lean ──AXLE──► refute_ok   (negation or finite counterexample)

  prove_ok ∧ refute_ok  →  BLOCKED   (bug in statement or checker — never silent pick)
  refute_ok only        →  REFUTED
  prove_ok only         →  continue lint + attest → VERIFIED or THEATER-BLOCKED
  neither               →  FAILED
```

```bash
# Prove only
python3 scripts/settle.py Brockian/Foo.lean --env lean-4.32.0

# Dual race
python3 scripts/settle.py Brockian/Foo.lean \
  --refute aristotle/foo-neg/target.lean \
  --env lean-4.32.0 --json
```

Historical statement-fidelity refutations (Aristotle): see `PORT-QUEUE.md`  
(`boundedV_isLimitPoint`, `radius_tendsto_zero_iff`) — treat as REFUTED narrative; re-settle with an explicit negate module when available.

---

## 4. REFUTED register (two layers)

### 4.1 Theorem registry (`gen_registry`)

Today theorem-level registers are:  
`PROVED | UNVERIFIED | COMPUTATION | CONDITIONAL | DISCHARGED | DEFINITION | CONJECTURE`.  

There is **no** theorem-level `REFUTED` row yet. Refutations are recorded via:

1. settle certificate `verdict=REFUTED`, and/or  
2. problem-level ledger (preferred for attack pipeline).

### 4.2 Problem ledger (`pipeline`)

`pipeline/core/ledger.derive_problem_register` precedence:

1. **BLOCKED** — theater or dual-prover disagreement  
2. **REFUTED** — `latest_result == "refuted"` / attempt results contain `refuted`  
3. **PROVED** — only if `lean_axle_verified` + `axioms_clean`  
4. DISTILLED / LITERATURE / CONDITIONAL / COMPUTATION / SCAFFOLD / PARTIAL / OPEN  

```bash
python3 -m pipeline.scripts.pipeline_cli attempt <id> \
  --mode refute --result refuted \
  --artifact path/to/counterexample.lean \
  --note "certified counterexample"

python3 -m pipeline.scripts.pipeline_cli ledger
```

---

## 5. Operator runbook (happy path)

From **repo root** `brockian-mathematics/`:

### 5.1 Dry plan (no network) — prefer first

```bash
python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean
# optional: restrict decls, dual-race, pipeline id
python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean thmA thmB \
  --refute aristotle/foo-neg/target.lean \
  --pipeline-id distill-etp-stage2
```

Copies the exact `attest.py` + `gen_registry.py` (+ `settle` / pipeline) lines.

### 5.2 Settle (one-shot certificate; calls AXLE)

Requires `AXLE_API_KEY` in the environment.

```bash
export AXLE_API_KEY=...   # from vault if needed
python3 scripts/no_theater_lint.py Brockian/Foo.lean
python3 scripts/settle.py Brockian/Foo.lean --env lean-4.32.0
# → registry/certificates/Foo.json
```

### 5.3 Commit-grade attestation + registry join

`settle` previews registers but **registry join still requires committed attestations**:

```bash
# names = short decl names; namespace = Brockian.Foo
python3 scripts/attest.py Brockian/Foo.lean Brockian.Foo \
  decl1 decl2 ... --env lean-4.32.0
# → registry/attestations/Foo.json

# Root import required or gen_registry skips the stem
# Edit Brockian.lean:  import Brockian.Foo

python3 scripts/gen_registry.py
# → registry/theorems.json + REGISTRY.md
```

### 5.4 Pipeline ledger (problem-level)

```bash
python3 -m pipeline.scripts.pipeline_cli attempt <problem-id> \
  --mode formalize --result proved \
  --axioms-clean --axle-verified \
  --artifact Brockian/Foo.lean \
  --artifact registry/attestations/Foo.json \
  --artifact registry/certificates/Foo.json

python3 -m pipeline.scripts.pipeline_cli ledger
```

Integration contract for multi-agent work: [`docs/AGENT-COORDINATION.md`](AGENT-COORDINATION.md).

---

## 6. SAIR Stage 2 path

Card: `distill-etp-stage2`  
(`pipeline/catalog/distillation/distill-etp-stage2.json`)

| Stage | Artifact | Gate |
|-------|----------|------|
| Stage 1 | Cheatsheet ≤ 10KB | `pipeline_cli distill-check` |
| Stage 2 | Lean proof **or** explicit finite counterexample | settle prove **or** settle `--refute` |

```bash
# Stage 1
python3 -m pipeline.scripts.pipeline_cli distill-check \
  pipeline/distill/cheatsheets/etp_v0.txt

# Stage 2 — proof leg
python3 scripts/pipeline_attest_bridge.py Brockian/EqImp.lean \
  --pipeline-id distill-etp-stage2
# then run printed attest/settle commands

# Stage 2 — counterexample leg
python3 scripts/settle.py Brockian/EqImp.lean \
  --refute path/to/counterexample_magma.lean --env lean-4.32.0
python3 -m pipeline.scripts.pipeline_cli attempt distill-etp-stage2 \
  --mode refute --result refuted --artifact path/to/counterexample_magma.lean
```

**SAIR.foundation tracker** (`sair-program-tracker`): meta only — spawn child cards;  
**never auto-submit** to competition; human review + AI-disclosure per SAIR rules  
([pipeline design §11](superpowers/specs/2026-08-02-problem-attack-pipeline.md)).

---

## 7. Verification legs (PROVED certificate)

All of the following for a theorem-level **PROVED** register:

1. **AXLE** independent check at named env (default `lean-4.32.0`)  
2. **no_theater_lint** — 0 blocking findings  
3. **Axioms** ⊆ `{propext, Classical.choice, Quot.sound}`; no `native_decide` (→ COMPUTATION)  
4. **Root import** in `Brockian.lean` so `gen_registry` includes the attestation stem  

`settle` enforces 1–3 for `VERIFIED`; `gen_registry` enforces 1+3 (+ provenance) for `PROVED`.

---

## 8. Concurrent-agent safety (do not clobber)

| Safe | Unsafe |
|------|--------|
| Run `pipeline_attest_bridge.py` (read-only) | Overwrite another agent’s `registry/attestations/X.json` without re-attest |
| Write new module `Brockian/New.lean` you own | Bulk-edit `gen_registry.py` / `attest.py` mid-swarm |
| Append pipeline attempt on **your** problem id | Force `register: PROVED` in YAML/JSON by hand |
| Emit certificate under gitignored `registry/certificates/` | Commit certificates as if they replaced attestations |
| Claim ownership in `AGENT-COORDINATION.md` | Dual-write same Lean module without coordination |

Certificates are gitignored so parallel settles do not dirty shared commits;  
**publish** only via attest → gen_registry after root import.

---

## 9. Gaps to close for `attempt → attest → ledger`

See also design “Next slices” in  
[`docs/superpowers/specs/2026-08-02-problem-attack-pipeline.md`](superpowers/specs/2026-08-02-problem-attack-pipeline.md) §10 / §13.

| # | Gap | Today | Desired |
|---|-----|-------|---------|
| 1 | **Auto-wire** `pipeline_cli attempt --mode formalize` → lint + attest | Manual; bridge only prints | Optional `--run-attest` when `formal_targets[].path` set |
| 2 | **Certificate → ledger join** | Operator copies paths into `--artifact` | Helper: `settle` exit + write attempt JSON / `pipeline join-cert` |
| 3 | **Theorem-level REFUTED** | Only problem-level + certificate | Optional provenance / registry flag for refuted names |
| 4 | **settle does not write attestations** | Certificate gitignored; registry needs separate `attest.py` | Documented; optional `--also-attest` on settle (careful: concurrent overwrites) |
| 5 | **Root-import gate** | Easy to attest non-imported stem (skipped) | Bridge already prints import hint; CI smell check exists (`list_attestation_smells`) |
| 6 | **Dual-race packaging** | Manual `--refute` path | Catalog `formal_targets` with `{kind: counterexample, path}` auto-passed to settle |
| 7 | **SAIR Stage 2 harness** | Card + manual Lean | Packaging for proof/counterexample + human submit checklist |
| 8 | **Multi-env matrix** | Single `--env` | Second settle/attest @ `lean-4.28.0` for high-stakes |
| 9 | **Observatory pipeline surface** | Theorem observatory only | `observatory/pipeline.html` from `ledger/problems.json` |
| 10 | **gen_program_report** | Not present (Agent REPORT may own) | SAIR/program rollup from certificates + ledger — **do not invent if REPORT is active** |

**Minimal close for “attempt → attest → ledger” without large rewrites:**

```bash
# 0. plan
python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean --pipeline-id <id>

# 1–3. execute printed lint / attest / gen_registry (and settle)

# 4. ledger
python3 -m pipeline.scripts.pipeline_cli attempt <id> ...
python3 -m pipeline.scripts.pipeline_cli ledger
```

---

## 10. Quick reference

```bash
# Help
python3 scripts/settle.py --help
python3 scripts/attest.py --help
python3 scripts/pipeline_attest_bridge.py --help

# Dry plan (no AXLE)
python3 scripts/pipeline_attest_bridge.py Brockian/FranklinFixedPoint.lean --json | head

# Full settle (needs AXLE_API_KEY)
python3 scripts/settle.py Brockian/FranklinFixedPoint.lean --env lean-4.32.0

# Registry from committed attestations
python3 scripts/gen_registry.py

# Problem pipeline
python3 -m pipeline.scripts.pipeline_cli list --domain distillation
python3 -m pipeline.scripts.pipeline_cli show distill-etp-stage2
python3 -m pipeline.scripts.pipeline_cli ledger
```

**Related docs:**  
[AGENT-COORDINATION](AGENT-COORDINATION.md) · [REGISTRY-HYGIENE-QUEUE](REGISTRY-HYGIENE-QUEUE.md) · [pipeline README](../pipeline/README.md) · [problem-attack spec](superpowers/specs/2026-08-02-problem-attack-pipeline.md)
