# Overleaf corpus audit — 60 projects vs the verified core (2026-08-02)

Triage of the 60-project Overleaf export (`Overleaf Projects (62 items).zip`) for harvestable content,
in the intake-ledger tradition: **gold** (new + formalizable), **overclaim** (skip — open problem
asserted proved), **non-math** (skip), **superseded** (already in core). The verified core is the
arbiter; nothing enters as PROVED without the AXLE + firewall gate.

## Triage

### GOLD — genuinely new, honest, formalizable (the harvest)
The **Erdős problems** — and they already follow our discipline (analytic cores isolated as *named
conjectures*, only elementary reductions proved, conditional conclusions clearly marked). New to the
core (we have zero Erdős content); the roadmap-#5 scoreboard done right.

| Project | Problem | Unconditional (formalizable now) | Conditional (rung-3, named hyp) |
|---------|---------|----------------------------------|----------------------------------|
| `Erdos 304` (= Erdős #320, "Spectral Completion") | spectral/collision asymptotic | reduction lemmas (to `U(N)`, entropy reduction), robust big-O | main asymptotic under 3 named conjectures (kernel-tightness, collision divisor-sum, **D₅-symmetric renormalization** — ties to our D₅ work) |
| `Erdos Problem` ("Pinned Distances, Radial Operators") | Erdős pinned-distance | energy–entropy bridge, Rényi-entropy monotonicity, `H ≤ log d`, grid construction achieving the exponent; cites Pach–de Zeeuw (real) | general pinned bound conditional on the isosceles bound |
| `Erdos Problem 236` | growth of `f(n)` | trivial upper bound; Fourier representation | main bound conditional on **PDCH/BPRH** (GRH-strength named conjecture) |
| `Operator`, `Rigorous operator` | Erdős + operator framing | (to survey) | likely conditional |

**Caveat:** these are *analytic* (asymptotics, exponential sums, entropy). Formalize **selectively** —
the elementary unconditional lemmas + the conditional theorem *statements* as named-hypothesis
CONDITIONALs. Do **not** attempt the analytic cores (they are the named conjectures, deliberately open).

### SUPERSEDED / to spot-check
- `files (7)`, `LEAN FILE D5` (both 14 thms, contain `sorry`), `LEAN FORMALIZATION JAN 25` — source Lean
  drafts (cyclotomic/dihedral/golden/pentagon). Almost certainly superseded by the AXLE-verified core;
  spot-check only for any decl not yet covered. **Their `sorry`s mean they are NOT importable as-is.**
- `Brockian Spectral Rigidity V1/V2/V3`, `P5 Paper on pentagon`, `Pentagon Program/enhanced`,
  `Toric Golden Ratio`, `Toric pentagonal`, `Penrose*` — the pentagon/golden/Penrose corpus, largely
  reflected in `Spectral`, `CycleSpectrumFamily`, `PentagonIsotypic`, `PenroseL2`. Check toric/Penrose
  for any new *finite* lemma; otherwise covered.
- **Weil cluster** (`Brock-Weil`, `Weil Arithmetic Hinge`, `Imath`, `implementation mathematics`,
  `i math 2`) — `admissib`+`weil` keywords suggest finite admissibility content possibly reusable; worth
  a targeted read for any finite lemma not in `Admissibility*`. Do NOT harvest any "Weil conjectures
  proved" framing.

### OVERCLAIM — skip for formalization (open problem asserted proved)
The RH-proof cluster: `RIEMANN BROCK SUBMIT` (16 thms), `Oct 7 Tier I/II` (39 thms), `Riemann Brock
Proof`, `New Riemann Brock` (14), `RIEMANN BROCK`, `Riemann Brock v1/v2`, `Riemann Brock Polya Project`,
`March 21 Riemann Brock`, `Front and back Riemann`, `Riemann Hypothesis Torus`, and the named-frame
essays (`Perelman`, `Deligne`, `Poincare`, `Gauss`, `Tao`, `Dvorak`, `Einstein Waves`, `Ricci Flows`).
RH is **open**; our core keeps it a CONDITIONAL scaffold (`RiemannScaffold`, ξ functional equation +
zero correspondence). These papers may contain a reusable *conditional* ξ/operator lemma, but **no RH
"proof" enters the registry** — the firewall forbids it.

### NON-MATH — skip
`Cryptography`, `DARPA`, `Supreme Court Memo`, `Supreme Court of Ohio`, `Filing`, `Pentagonal Machine
Patent`, `Pentagonal Turing Machine Patent(s)`, `EXPMATH TECH OVERVIEW` — applications / legal / patent.

## Recommendation

1. **Harvest the Erdős problems as HONEST conditional formalizations** — unconditional elementary lemmas
   (trivial bounds, entropy monotonicity, reductions, grid constructions) as PROVED, and the main
   asymptotics as CONDITIONAL on their *named* conjectures (rung: literature/open). This adds genuine
   Erdős content (the scoreboard) without overclaiming, and `Erdos 304`'s D₅-renormalization conjecture
   even links to our D₅ core. Selective — analytic cores stay the named open conjectures.
2. **Spot-check** the source Lean drafts (`files (7)`, `LEAN FILE D5`) and the Weil-admissibility cluster
   for any finite decl not yet in the core; import only what passes the gate (their `sorry`s bar direct import).
3. **Do NOT** touch the RH-proof cluster or essays as proved content; the ξ scaffold stays conditional.

**Bottom line:** the pull is worth it for exactly one seam — the Erdős problems, formalized as honest
conditionals. The rest is either already in the core, RH-overclaim the firewall rejects, or non-math.
