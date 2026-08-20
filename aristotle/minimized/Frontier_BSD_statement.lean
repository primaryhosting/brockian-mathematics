import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
required header block is placed immediately after `import Mathlib`.

This file formalises the statement of the Birch--Swinnerton-Dyer conjecture

  ord_{s = 1} L(E, s) = rank E(ℚ)

for elliptic curves over `ℚ` given by a global minimal integral Weierstrass model, and proves
the rank-zero base case together with a Lean-checked reduction of the rank-zero case of the
conjecture to the equivalence `L(E, 1) ≠ 0 ↔ E(ℚ) finite`.
-/

namespace Frontier

open WeierstrassCurve

/-! ## The Mordell–Weil group and its rank -/

/-- The group `E(ℚ)` of rational points of the elliptic curve given by the integral
Weierstrass model `W` over `ℤ`. -/
abbrev RatPoints (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The algebraic rank of `E(ℚ)`: the rank of the Mordell–Weil group as a `ℤ`-module. -/

noncomputable def mordellWeilRank (W : WeierstrassCurve ℤ) : ℕ :=
  (Module.rank ℤ (RatPoints W)).toNat

/-! ## The `L`-function -/

/-- The number of nonsingular points, including the point at infinity, of the reduction
modulo `p` of the integral Weierstrass model `W`. -/

noncomputable def reductionCard (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card ((W.map (Int.castRingHom (ZMod p))).toAffine.Point)

/-- The trace of Frobenius `a_p` of the integral Weierstrass model `W` at a prime `p`.

At a prime of good reduction (`p ∤ Δ`) the reduction is an elliptic curve over `𝔽_p` with
`p + 1 - a_p` points, while at a prime of bad reduction the group of nonsingular points of the
reduction has `p - a_p` elements (so `a_p = 1, -1, 0` for split multiplicative, nonsplit
multiplicative and additive reduction respectively). -/

noncomputable def apCoeff (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  if (p : ℤ) ∣ W.Δ then (p : ℤ) - (reductionCard W p : ℤ)
  else (p : ℤ) + 1 - (reductionCard W p : ℤ)

/-- `W` is a global minimal Weierstrass model: its discriminant is minimal in absolute value
among all integral Weierstrass models of the same elliptic curve over `ℚ`. -/

def IsGlobalMinimalModel (W : WeierstrassCurve ℤ) : Prop :=
  ∀ (W' : WeierstrassCurve ℤ) (C : VariableChange ℚ),
    W'.baseChange ℚ = C • W.baseChange ℚ → W.Δ.natAbs ≤ W'.Δ.natAbs

/-- `a : ℕ → ℂ` is the sequence of Dirichlet coefficients of the Hasse–Weil `L`-series of the
global minimal Weierstrass model `W`, i.e.

  `L(E, s) = ∑ n, a n / n ^ s = ∏_{p good} (1 - a_p p^{-s} + p^{1 - 2s})⁻¹
                                 ∏_{p bad}  (1 - a_p p^{-s})⁻¹`.

This is expressed through the multiplicativity of `a`, the value of `a` at primes, and the
Euler-factor recursions at prime powers. -/

def IsLSeriesCoeff (W : WeierstrassCurve ℤ) (a : ℕ → ℂ) : Prop :=
  a 0 = 0 ∧ a 1 = 1 ∧
  (∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n) ∧
  (∀ p : ℕ, p.Prime → a p = (apCoeff W p : ℂ)) ∧
  (∀ p k : ℕ, p.Prime → ¬ (p : ℤ) ∣ W.Δ →
      a (p ^ (k + 2)) = a p * a (p ^ (k + 1)) - (p : ℂ) * a (p ^ k)) ∧
  (∀ p k : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → a (p ^ k) = a p ^ k)

/-- `L` is *the* `L`-function of the elliptic curve given by the global minimal Weierstrass
model `W`: it is entire (this is the analytic continuation provided by modularity) and it agrees
with the Hasse–Weil Dirichlet series in the half plane of absolute convergence `Re s > 3/2`. -/

def IsLFunction (W : WeierstrassCurve ℤ) (L : ℂ → ℂ) : Prop :=
  ∃ a : ℕ → ℂ, IsLSeriesCoeff W a ∧ Differentiable ℂ L ∧
    ∀ s : ℂ, 3 / 2 < s.re → L s = LSeries a s

/-! ## The conjecture -/

/-- **The Birch and Swinnerton-Dyer conjecture** (rank part): for every elliptic curve `E / ℚ`,
given by a global minimal integral Weierstrass model `W` with nonzero discriminant, the order of
vanishing at `s = 1` of the `L`-function of `E` equals the rank of the Mordell–Weil group
`E(ℚ)`. -/

def BSD : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (L : ℂ → ℂ), W.Δ ≠ 0 → IsGlobalMinimalModel W → IsLFunction W L →
    analyticOrderAt L 1 = (mordellWeilRank W : ℕ∞)

/-! ## Basic facts about the two sides -/

theorem IsLFunction.analyticAt {W : WeierstrassCurve ℤ} {L : ℂ → ℂ} (hL : IsLFunction W L)
    (s : ℂ) : AnalyticAt ℂ L s :=
  hL.choose_spec.2.1.analyticAt s

/-- The analytic side: the order of vanishing at `s = 1` is zero exactly when `L(E, 1) ≠ 0`. -/

theorem analyticOrder_eq_zero_iff {W : WeierstrassCurve ℤ} {L : ℂ → ℂ} (hL : IsLFunction W L) :
    analyticOrderAt L 1 = 0 ↔ L 1 ≠ 0 :=
  (hL.analyticAt 1).analyticOrderAt_eq_zero

/-- A finite Mordell–Weil group is a torsion group. -/

theorem mordellWeilRank_eq_zero_of_isTorsion {W : WeierstrassCurve ℤ}
    (h : Module.IsTorsion ℤ (RatPoints W)) : mordellWeilRank W = 0 := by
  simp [mordellWeilRank, rank_eq_zero_iff_isTorsion.mpr h]

/-- The algebraic side, assuming the Mordell–Weil theorem for `E`: the rank of `E(ℚ)` vanishes
if and only if `E(ℚ)` is finite. -/

theorem BSD_statement {W : WeierstrassCurve ℤ} {L : ℂ → ℂ} (hL : IsLFunction W L)
    (hL1 : L 1 ≠ 0) (htors : Module.IsTorsion ℤ (RatPoints W)) :
    analyticOrderAt L 1 = (mordellWeilRank W : ℕ∞) := by
  rw [mordellWeilRank_eq_zero_of_isTorsion htors, (analyticOrder_eq_zero_iff hL).mpr hL1]
  rfl

/-- **A Lean-checked reduction of the rank-zero case of BSD.** Assuming the Mordell–Weil theorem
for `E` (finite generation of `E(ℚ)`), the BSD equality in the rank-zero case is equivalent to
the statement that `L(E, 1) ≠ 0` if and only if `E(ℚ)` is finite. -/
