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

## Proof verification (2026-08-02) — "ensure the proofs actually work"

Referee agents read the FULL proofs (not just statements); finite content was AXLE-formalized as the
definitive test. First finding:

### RH-proof cluster — VERIFIED TO NOT PROVE RH (four exact gaps)
Flagship `RIEMANN BROCK SUBMIT/main.tex` ("Complete Spectral-Geometric Resolution of RH", Mar 2025)
claims a self-adjoint `B̂ = −Δ_B + V` on `ℍ/Γ₀(5)` with eigenvalues bijecting the zeta zeros. It does
**not** prove RH:
1. **Determinant identity asserted, not proved** — `det_reg(s−B̂)=C·ζ(s+½)·G(s)` (§3.2) has no derivation
   ("Appendix C" is a generic template); the sibling `Riemann Brock Proof` says "through careful analysis
   … we establish the identity" — a prose `sorry`. This identity IS the Hilbert–Pólya open core.
2. **Circular bijection** — writes `ρ=½+iγ` to derive `λ=γ²+¼` (assumes RH to prove RH); internally
   contradictory (`λ=−γ²` vs `λ=γ²+¼`).
3. **Numerics as proof** — "holds for j≤10⁹ with error <10⁻¹²" (finite ≠ all), and the table contradicts
   it (`λ₁=199.936` vs `γ₁²+¼=200.040`, ~0.1 off).
4. **Ill-defined operator** — `V` piles all primes onto 5 fixed centers with coefficients summing to
   `∑ log p/p` (divergent); Kato–Rellich applied to a divergent potential.

**Cross-check:** the honest sibling `Oct 7 Tier I/II` itself splits Tier-I (unconditional scaffold:
KLMN self-adjointness, trace-class, relative-determinant existence) from Tier-II (CONJECTURAL:
PGPT + Conjecture G ⇒ correspondence ⇒ RH) — exactly the shape of our `RH_of_BrockianSystem`.
`Brockian/RiemannScaffold.lean` already encodes the honest state (Part 1 PROVED: ξ functional eq +
ζ→ξ; Part 2 CONDITIONAL rung OPEN: `RH_of_BrockianSystem`, Gate-0 note = no BrockianSystem constructed).
**The papers' content beyond the scaffold is precisely the unproven `eigen_of_zero` inhabitation — the
firewall's conditional line is vindicated.** No RH content enters the registry.

(Erdős proof verifications appended as they complete.)

### Erdős #236 — math sound & honestly conditional; paper's own Lean OVERSTATED; one lemma harvested
Referee read + machine check:
- **Trivial bound `f(n) ≤ ⌊log₂n⌋+1` — SOUND, UNCONDITIONAL, AXLE-VERIFIED** (harvested as
  `Brockian.Erdos236.f_le_log`, on the paper's own `f`; the paper's cited lemma name did not exist —
  used Mathlib `Nat.le_log_of_pow_le`).
- **Main bound — sound, NON-circular, conditional on PDCH/BPRH** (GRH-strength, honestly labeled).
- **Defects found:** the Fourier step `g_N(n)=f(n)` glosses a wrap-around justification; and the
  paper's OWN Lean overstates — core lemma `f_le_sup_SD` has an elided (`...`) load-bearing body,
  `FourierIdentity` is assumed not derived, and the written `hSup` is broken/false at `j=0`
  (`|C(n,0)|≈n` exceeds the PDCH bound). Only the clean unconditional bound harvested; the conditional
  main theorem is NOT taken as ours.
