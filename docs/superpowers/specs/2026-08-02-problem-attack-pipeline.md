# Problem Attack Pipeline — Multi-Domain Design

**Date:** 2026-08-02  
**Status:** design + v0 scaffold (built)  
**Repo:** `brockian-mathematics` (`pipeline/` package)  
**Parent process:** Brockian verified-core (registers, AXLE, multi-agent attack, no theater)

---

## 0. Why this exists

The Brockian program already runs a **process against hard problems**:

1. Name the claim honestly (never overclaim RH / Goldbach / Gate 1).
2. Decompose into finite / local / conditional / schema layers.
3. Attack with multi-agent fleets (Aristotle race, Grok finite algebra, Claude synthesis).
4. Verify independently (local lake + `#print axioms` + **AXLE**).
5. Derive a **register** from facts — never hand-assert PROVED.
6. Publish only ledger-backed claims (registry → paper → observatory).

That process works for math and physics scaffolding. This design **generalizes** it into a single pipeline that can intake and attack:

| Source | What it is | Success criterion |
|--------|------------|-------------------|
| **Erdős problems** | [erdosproblems.com](https://www.erdosproblems.com/) — ~1217 problems, ~46% solved | Open → partial scaffold → formal/comp certificate → literature-closed |
| **Distillation challenges** | SAIR Mathematics Distillation (Equational Theories Stage 1/2) | ≤10KB cheat sheet lifting weak-model accuracy; Stage 2: Lean proof or counterexample |
| **SAIR.foundation** | Tao + laureate AI-for-science programs | Challenge-specific harness; scientific-method rigor on AI outputs |
| **Mathematics** | Number theory, analysis, algebra, combinatorics, geometry | Lean/Mathlib + AXLE; or computational certificate |
| **Physics** | Classical / continuum / statistical | Model formalization + numerical sanity + literature |
| **Computer science** | Algorithms, complexity, systems correctness | Implementation + tests + optional formal proof |
| **Quantum physics** | Operators, spectra, information, many-body | Formal model (Lean/Julia/QuTiP) + bounds + no overclaim |

**Non-goals (v0):**
- Auto-solving millennium problems.
- Submitting to SAIR competition without human review.
- Replacing the Brockian Lean registry (this pipeline **feeds** it when targets are formal).

---

## 1. Process (domain-agnostic)

```
                    ┌─────────────┐
   sources ───────► │   INTAKE    │  normalize → Problem card
                    └──────┬──────┘
                           ▼
                    ┌─────────────┐
                    │  TRIAGE     │  difficulty, formalizable?,
                    │             │  attack mode, risk tier
                    └──────┬──────┘
                           ▼
                    ┌─────────────┐
                    │ DECOMPOSE   │  lemmas, reductions, scaffolds,
                    │             │  refutation targets
                    └──────┬──────┘
                           ▼
              ┌────────────┴────────────┐
              ▼                         ▼
       ┌────────────┐            ┌────────────┐
       │   ATTACK   │            │  REFUTE    │  dual race
       │ (provers)  │            │ (search)   │
       └─────┬──────┘            └─────┬──────┘
             └────────────┬────────────┘
                          ▼
                   ┌─────────────┐
                   │  VERIFY     │  backend by domain
                   └──────┬──────┘
                          ▼
                   ┌─────────────┐
                   │  LEDGER     │  derive register (never hand-assert)
                   └──────┬──────┘
                          ▼
                   ┌─────────────┐
                   │  DISTILL    │  cheat sheet / brief / claim
                   └──────┬──────┘
                          ▼
                   ┌─────────────┐
                   │  PUBLISH    │  only ledger-backed claims
                   └─────────────┘
```

### 1.1 Non-negotiable rules (carried from Brockian)

1. **Register is derived**, never hand-asserted (same spirit as `derive_register` in `scripts/gen_registry.py`).
2. **No theater** — vacuous hypotheses, ex-falso “proofs,” title inflation, and misformalization are lint-rejected.
3. **Independent verification** when a formal artifact exists (AXLE / second Lean env / dual prover).
4. **Honest open cores** stay OPEN or CONDITIONAL; schemas are labeled as such.
5. **Surgical multi-agent commits** — no clobber; explicit paths; coordination queue.
6. **Overclaim firewall** — public claims ⊆ ledger entries with allowed registers.

---

## 2. Problem card schema

Every problem is a versioned JSON document under `pipeline/catalog/<domain>/`.

```json
{
  "id": "erdos-90",
  "domain": "erdos",
  "title": "Unit distance problem (planar)",
  "statement": "...",
  "source": {
    "url": "https://www.erdosproblems.com/90",
    "citation": "Erdős ...",
    "external_status": "solved"
  },
  "status": "open | partial | scaffolded | conditional | proved | refuted | distilled | blocked",
  "difficulty": 1-5,
  "tags": ["combinatorics", "geometry"],
  "formal_targets": [
    {
      "kind": "lean_theorem",
      "name": "Brockian.Erdos.UnitDistance....",
      "path": null
    }
  ],
  "attack_modes": ["literature", "formalize", "compute", "distill"],
  "verification": {
    "backend": "lean_axle | literature | compute | distillation_harness | hybrid",
    "criteria": ["..."]
  },
  "risk_tier": 1,
  "notes": "",
  "attempts": [],
  "ledger_refs": []
}
```

`risk_tier` (legal/scientific stakes):
- **1** — pure math formalization / distillation experiments (ship freely with verification).
- **2** — physics model claims with experimental implications (human confirm).
- **3** — anything that could be misread as a solved millennium / security break (block + review).

---

## 3. Registers (generalized)

| Register | Meaning | How derived |
|----------|---------|-------------|
| **OPEN** | No closing artifact | Default on intake |
| **SCAFFOLD** | Named schema / defs / reductions only | Formal defs exist; no closed theorem |
| **CONDITIONAL** | Proved under named hypothesis | `conditional_rung` set |
| **COMPUTATION** | Finite check / numeric / decide | `native_decide` or compute cert |
| **DISTILLED** | Cheat sheet met harness threshold | Distillation backend pass |
| **PROVED** | Independent formal verification | Lean axioms clean + AXLE verified (or equivalent formal backend) |
| **REFUTED** | Counterexample / contradiction certified | Dual-prover or explicit model |
| **DISCHARGED** | Prior CONDITIONAL now closed | Provenance link to discharging theorem |
| **BLOCKED** | Misformalization / theater / policy | Lint or human gate |
| **LITERATURE** | External solution accepted, not re-formalized | Citation + human accept (honest label, not PROVED) |

Brockian Lean theorems continue to use the existing registry; the pipeline ledger **points into** `registry/theorems.json` when a formal target lands.

---

## 4. Domain adapters

### 4.1 Erdős (`pipeline/adapters/erdos.py`)

- **Intake:** manual seed cards + optional scrape of problem metadata from erdosproblems.com.
- **Triage:** prefer open problems with combinatorial / finite-check structure (high yield for our stack).
- **Attack:**
  - literature status sync (do not re-claim solved problems as our PROVED),
  - formal scaffold in Lean when statement is formalizable,
  - computational search for small counterexamples / bounds.
- **Verify:** literature register **or** Lean+AXLE if we re-prove.
- **Guard:** AI “solutions” without independent check → BLOCKED (see community misinformation risk).

### 4.2 Distillation / SAIR equational (`pipeline/adapters/distillation.py`)

Aligned with [SAIR Mathematics Distillation Challenge](https://terrytao.wordpress.com/2026/03/13/mathematics-distillation-challenge-equational-theories/):

- **Stage 1 artifact:** cheat sheet ≤ **10 KB** improving weak-model T/F accuracy on equational implications.
- **Stage 2 direction:** probability + **Lean proof or explicit counterexample**.
- **Pipeline job:**
  1. Maintain local technique catalog (from ETP / our attacks).
  2. Compress into `pipeline/distill/cheatsheets/*.txt` with size gate.
  3. Score against public playground set when available; log accuracy.
  4. Promote to DISTILLED only if size + score gates pass.
- **Export:** human review before any competition submit.

### 4.3 SAIR general (`pipeline/adapters/sair.py`)

- Track challenge IDs, program links, submission constraints.
- Prefer cooperative SAIR programs when announced; competitive tracks go through DISTILL + human gate.
- Science-for-AI rule: every AI claim gets a verification backend.

### 4.4 Mathematics (`pipeline/adapters/math.py`)

- Default path into Brockian Lean modules + existing `attest.py` / `gen_registry.py`.
- Decomposition patterns: finite → CRT → sieve → spectral → conditional schema.

### 4.5 Physics / Quantum (`pipeline/adapters/physics.py`, `quantum.py`)

- Problem → mathematical model card → formal or numeric target.
- Prefer operator theory / spectral problems that share Gate-1 / Weyl infrastructure.
- Registers: SCAFFOLD for models; PROVED only for mathematical theorems about the model; experimental claims stay LITERATURE/CONDITIONAL.

### 4.6 Computer science (`pipeline/adapters/cs.py`)

- Correctness: tests + optional Lean/Dafny/// formal.
- Complexity: reductions as CONDITIONAL or LITERATURE unless formalized.
- Implementation artifacts live under `pipeline/artifacts/cs/`.

---

## 5. Attack modes (multi-agent)

| Mode | Agent role | Best for |
|------|------------|----------|
| `formalize` | Lean author + AXLE | Math / CS correctness / Stage 2 distill |
| `refute` | Counterexample search + Aristotle race | Equational, combinatorial, finite |
| `compute` | Numeric / SAT / sieve / Monte Carlo | Bounds, small cases, physics |
| `distill` | Compress technique → cheat sheet | SAIR Stage 1 |
| `literature` | Status sync + citation | Erdős solved; physics experiment |
| `decompose` | Human/LLM reduction plan | Hard OPEN problems |
| `dual_prover` | Two independent provers must agree | High-stakes PROVED |

**Disagreement protocol:** if dual provers disagree → status `blocked` until human triage (no silent PROVED).

---

## 6. Verification backends

```
lean_axle:
  lake build → #print axioms ⊆ {propext, Classical.choice, Quot.sound}
  → scripts/attest.py → AXLE verified → derive PROVED

literature:
  source.external_status + citation + human accept → LITERATURE

compute:
  reproducible script + golden output hash → COMPUTATION

distillation_harness:
  size ≤ 10240 bytes + accuracy ≥ threshold on eval set → DISTILLED

hybrid:
  any combination; strictest register wins for public claim
```

---

## 7. Filesystem layout

```
pipeline/
  README.md
  schema/problem.schema.json
  catalog/
    erdos/          # problem cards
    distillation/
    sair/
    math/
    physics/
    cs/
    quantum/
  adapters/         # domain intake + triage helpers
  core/
    schema.py       # load/validate cards
    ledger.py       # derive register
    stages.py       # intake → ... → publish
    triage.py
    attack_queue.py
  distill/
    cheatsheets/
    score.py
  scripts/
    pipeline_cli.py # main entry
    seed_catalog.py
    sync_status.py
  tests/
  artifacts/        # attempt outputs (gitignored large blobs)
  ledger/
    problems.json   # generated summary
    LEDGER.md       # human table
```

Integration with Brockian:
- Formal targets that close → `Brockian/*.lean` + existing registry path.
- Pipeline ledger stores **problem-level** status; theorem-level stays in `registry/theorems.json`.

---

## 8. CLI (v0)

```bash
# list / filter
python3 -m pipeline.scripts.pipeline_cli list --domain erdos --status open

# show one card
python3 -m pipeline.scripts.pipeline_cli show erdos-90

# triage + write attack plan
python3 -m pipeline.scripts.pipeline_cli triage erdos-90

# record an attempt (formal / compute / distill)
python3 -m pipeline.scripts.pipeline_cli attempt erdos-90 \
  --mode formalize --note "scaffold lemmas" --result scaffold

# size-gate a cheatsheet
python3 -m pipeline.scripts.pipeline_cli distill-check pipeline/distill/cheatsheets/etp_v0.txt

# rebuild ledger
python3 -m pipeline.scripts.pipeline_cli ledger

# seed starter catalogs
python3 -m pipeline.scripts.seed_catalog
```

---

## 9. Seed priorities (first 30 days)

1. **Erdős open, combinatorial** — finite or graph-theoretic (attackable with compute + Lean).
2. **Distillation Stage-1 sheet** — compress ETP/Brockian equational tactics into ≤10KB; local score loop.
3. **SAIR program tracker** — cards for announced challenges; no auto-submit.
4. **Math** — link existing Brockian OPEN cores (Gate 1 LP continuous-bounded, free Laplacian Plancherel, RH schema) as pipeline cards so they appear in one attack queue.
5. **Quantum/physics** — Weyl/Schrödinger model cards sharing Gate-1 infrastructure.
6. **CS** — one correctness target (e.g. sieve implementation matching Lean counts).

---

## 10. Acceptance criteria (v0)

- [x] Design doc (this file).
- [x] JSON schema + Python validation.
- [x] Seed catalogs for all seven domain folders (≥1 card each; Erdős multi).
- [x] Register derivation unit-tested.
- [x] CLI: list / show / triage / attempt / distill-check / ledger.
- [x] Distill size gate (10 KB).
- [x] LEDGER.md generation.
- [ ] Live erdosproblems.com sync (optional; v1).
- [ ] Live SAIR playground scoring (optional; needs network + API).
- [ ] Auto-wire attempt → `attest.py` for Lean paths (v1).

---

## 11. Risk & ethics

- Do not publish “we solved Erdős #N” without LITERATURE accept or PROVED formalization.
- Distillation submissions: human review; disclose AI assistance per SAIR rules.
- Physics/quantum: mathematical theorems about models ≠ experimental claims.
- Cost control: attack queue prioritizes high-yield / low-risk-tier work (same spirit as circadian fleet).

---

## 12. Relation to experimental Axiom ideas

Prior experimental uses map cleanly:

| Experiment | Pipeline stage |
|------------|----------------|
| Dual-prover disagreement | VERIFY `dual_prover` |
| Multi-env matrix | lean_axle multi-env attest |
| Conditional discharge factory | DISCHARGED transitions |
| REFUTED register | REFUTED |
| Brockian-as-benchmark | catalog/math + scoring |
| Prose multi-formalization | formal_targets[] multi-kind |

---

## 13. Next implementation slices (after v0)

1. `sync_erdos.py` — pull open/solved metadata.
2. Lean attempt hook: `attempt --mode formalize` runs no_theater + attest when path set.
3. Observatory page `observatory/pipeline.html` from `ledger/problems.json`.
4. ACUTIS API: `GET /api/pipeline/status` for home dashboard.
5. Stage-2 equational harness: Lean counterexample / proof packaging.
