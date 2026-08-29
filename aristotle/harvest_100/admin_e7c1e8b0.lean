import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean 4 requires the `import` block to be the very first
command in a file, so the module docstring above is placed directly after it.

## Contents

* `Frontier.mordellWeilRank` : the algebraic rank of `E(ℚ)`, defined as the
  `ℚ`-dimension of `ℚ ⊗[ℤ] E(ℚ)` (as an element of `ℕ∞`, so that it is honest
  even without appealing to the Mordell–Weil theorem, which is not in Mathlib).
* `Frontier.IsHasseWeilLFunction` : the characterising properties of the
  Hasse–Weil `L`-function `L(E, s)` of an elliptic curve given by a global
  minimal integral Weierstrass model: it is entire (modularity) and on the
  half-plane `Re s > 3/2` it is given by the Euler product
  `∏_p (1 - a_p p^{-s} + ε_p p^{1-2s})⁻¹`.
* `Frontier.BSDConjecture` : the rank part of the Birch–Swinnerton-Dyer
  conjecture, `ord_{s=1} L(E, s) = rank E(ℚ)`.
* `Frontier.BSD_statement` : the Lean-checked reduction proved here — the
  conjecture implies, for every curve and every function satisfying the
  defining properties of its `L`-function, both the order-of-vanishing identity
  and the rank-zero criterion `L(E, 1) = 0 ↔ 1 ≤ rank E(ℚ)`.
* `Frontier.hasseWeilLFunction_unique` : the analytic rank appearing in the
  statement is well defined, i.e. an `L`-function satisfying the defining
  properties is unique.
* `Frontier.mordellWeilRank_eq_zero_iff_isTorsion` and
  `Frontier.mordellWeilRank_eq_zero_of_finite` : the base case, that the rank
  vanishes exactly for a torsion group of rational points, in particular for a
  curve with finitely many rational points.
* `Frontier.lFunction_one_ne_zero_of_finite` : the conjecture applied in that
  base case, giving `L(E, 1) ≠ 0` for a curve with finitely many rational
  points.
-/

open WeierstrassCurve

namespace Frontier

/-! ## The algebraic side: the Mordell–Weil rank -/

/-- The Mordell–Weil rank of the group `E(ℚ)` of rational points of an elliptic curve `E/ℚ`,
namely the `ℚ`-dimension of `ℚ ⊗[ℤ] E(ℚ)`, valued in `ℕ∞` (so an infinite rank, which the
Mordell–Weil theorem rules out, would be recorded as `⊤` rather than as junk). -/
noncomputable def mordellWeilRank (E : WeierstrassCurve ℚ) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℚ (TensorProduct ℤ ℚ E.toAffine.Point))

/-! ## The analytic side: the Hasse–Weil `L`-function -/

/-- The number of points of the reduction mod `p` of an integral Weierstrass model `W`, i.e.
`#E_ns(𝔽_p)`, counting the point at infinity. (Mathlib's `Point` type consists of the
*nonsingular* points, which is exactly what is needed at primes of bad reduction.) -/
noncomputable def reductionPointCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point

/-- A prime `p` is a prime of good reduction for the integral model `W` when it does not divide
the discriminant of `W`. (For a global minimal model this is the correct notion.) -/
def HasGoodReduction (W : WeierstrassCurve ℤ) (p : ℕ) : Prop := ¬ ((p : ℤ) ∣ W.Δ)

open Classical in
/-- The trace of Frobenius `a_p`. At a prime of good reduction `a_p = p + 1 - #E(𝔽_p)`; at a
prime of bad reduction the group of nonsingular points has order `p - a_p`, with `a_p = 1, -1, 0`
in the split multiplicative, non-split multiplicative and additive cases respectively. -/
noncomputable def traceOfFrobenius (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  if HasGoodReduction W p then (p : ℤ) + 1 - (reductionPointCount W p : ℤ)
  else (p : ℤ) - (reductionPointCount W p : ℤ)

open Classical in
/-- The coefficient `ε_p`, equal to `1` at primes of good reduction and to `0` at primes of bad
reduction. -/
noncomputable def eulerCoeff (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  if HasGoodReduction W p then 1 else 0

/-- The inverse `1 - a_p p^{-s} + ε_p p^{1-2s}` of the local Euler factor of `W` at `p`. -/
noncomputable def eulerFactorInv (W : WeierstrassCurve ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  1 - (traceOfFrobenius W p : ℂ) * (p : ℂ) ^ (-s)
    + (eulerCoeff W p : ℂ) * (p : ℂ) ^ (1 - 2 * s)

/-- `W'` is an integral Weierstrass model of the same elliptic curve as `W`, i.e. the two models
become isomorphic over `ℚ`. -/
def IsIntegralModelOf (W' W : WeierstrassCurve ℤ) : Prop :=
  ∃ C : VariableChange ℚ, C • W.map (Int.castRingHom ℚ) = W'.map (Int.castRingHom ℚ)

/-- `W` is a global minimal model: it is an elliptic curve (nonzero discriminant) whose
discriminant is of least absolute value among all integral models of the same curve. -/
def IsGlobalMinimalModel (W : WeierstrassCurve ℤ) : Prop :=
  W.Δ ≠ 0 ∧ ∀ W' : WeierstrassCurve ℤ, IsIntegralModelOf W' W → W.Δ.natAbs ≤ W'.Δ.natAbs

/-- The defining properties of the Hasse–Weil `L`-function `L(E, s)` of the elliptic curve given
by the integral Weierstrass model `W`:

* it is entire — this is the analytic continuation supplied by the modularity theorem;
* on the half-plane `Re s > 3/2` it is given by the Euler product
  `∏_p (1 - a_p p^{-s} + ε_p p^{1-2s})⁻¹`, the product being over all primes. -/
structure IsHasseWeilLFunction (W : WeierstrassCurve ℤ) (L : ℂ → ℂ) : Prop where
  entire : ∀ s : ℂ, AnalyticAt ℂ L s
  hasEulerProduct : ∀ s : ℂ, 3 / 2 < s.re →
    HasProd (fun p : Nat.Primes => (eulerFactorInv W (p : ℕ) s)⁻¹) (L s)

/-- **The Birch–Swinnerton-Dyer conjecture** (rank part): for every elliptic curve `E/ℚ`, given
by a global minimal Weierstrass model, the order of vanishing at `s = 1` of its Hasse–Weil
`L`-function equals the rank of the Mordell–Weil group `E(ℚ)`:
`ord_{s=1} L(E, s) = rank E(ℚ)`. -/
def BSDConjecture : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (L : ℂ → ℂ), IsGlobalMinimalModel W → IsHasseWeilLFunction W L →
    analyticOrderAt L 1 = mordellWeilRank (W.map (Int.castRingHom ℚ))

/-! ## Lean-checked reductions -/

/-- The analytic side of the conjecture is well posed: an entire function whose values on the
half-plane `Re s > 3/2` are given by the Euler product is unique. -/
theorem hasseWeilLFunction_unique {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsHasseWeilLFunction W L₁) (h₂ : IsHasseWeilLFunction W L₂) : L₁ = L₂ := by
  have hset : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
  have hev : L₁ =ᶠ[nhds (2 : ℂ)] L₂ := by
    filter_upwards [hset.mem_nhds hmem] with s hs
    exact (h₁.hasEulerProduct s hs).unique (h₂.hasEulerProduct s hs)
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun s _ => h₁.entire s) (fun s _ => h₂.entire s) hev

/-- The Mordell–Weil rank vanishes exactly when the group of rational points is a torsion group
(equivalently, in the presence of the Mordell–Weil theorem, when `E(ℚ)` is finite). -/
theorem mordellWeilRank_eq_zero_iff_isTorsion (E : WeierstrassCurve ℚ) :
    mordellWeilRank E = 0 ↔ Module.IsTorsion ℤ E.toAffine.Point := by
  rw [mordellWeilRank, IsBaseChange.rank_eq (TensorProduct.isBaseChange ℤ _ ℚ),
    ← rank_eq_zero_iff_isTorsion (R := ℤ), Cardinal.toENat_eq_zero]

/-- Base case: a curve with only finitely many rational points has Mordell–Weil rank zero. -/
theorem mordellWeilRank_eq_zero_of_finite (E : WeierstrassCurve ℚ)
    [Finite E.toAffine.Point] : mordellWeilRank E = 0 := by
  rw [mordellWeilRank_eq_zero_iff_isTorsion]
  intro P
  exact ⟨⟨(Nat.card E.toAffine.Point : ℤ),
      mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast Nat.card_pos.ne')⟩, by simp⟩

/-- A nonzero analytic order at a point is the same as vanishing there, for a function that is
analytic at that point. -/
theorem one_le_analyticOrderAt_iff {L : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ L z) :
    1 ≤ analyticOrderAt L z ↔ L z = 0 := by
  rw [ENat.one_le_iff_ne_zero, analyticOrderAt_ne_zero]
  simp [h]

/-- **BSD statement.** The Birch–Swinnerton-Dyer conjecture, as formalised in
`Frontier.BSDConjecture`, says exactly that for an elliptic curve `E/ℚ` given by a global minimal
Weierstrass model `W`, and for any function `L` satisfying the defining properties of the
Hasse–Weil `L`-function of `W`, the analytic order of vanishing of `L` at `s = 1` equals the rank
of `E(ℚ)`; and this implies the rank-zero criterion `L(E, 1) = 0 ↔ 1 ≤ rank E(ℚ)`.

The reduction from the order-of-vanishing identity to the rank-zero criterion is proved here,
unconditionally in the sense that the only input is the conjecture itself. -/
theorem BSD_statement (hBSD : BSDConjecture) (W : WeierstrassCurve ℤ) (L : ℂ → ℂ)
    (hW : IsGlobalMinimalModel W) (hL : IsHasseWeilLFunction W L) :
    analyticOrderAt L 1 = mordellWeilRank (W.map (Int.castRingHom ℚ)) ∧
      (L 1 = 0 ↔ 1 ≤ mordellWeilRank (W.map (Int.castRingHom ℚ))) := by
  refine ⟨hBSD W L hW hL, ?_⟩
  rw [← hBSD W L hW hL, one_le_analyticOrderAt_iff (hL.entire 1)]

/-- A consequence of the conjecture in the base case: if the curve has only finitely many
rational points, then its `L`-function does not vanish at `s = 1`. -/
theorem lFunction_one_ne_zero_of_finite (hBSD : BSDConjecture) (W : WeierstrassCurve ℤ)
    (L : ℂ → ℂ) (hW : IsGlobalMinimalModel W) (hL : IsHasseWeilLFunction W L)
    [Finite (W.map (Int.castRingHom ℚ)).toAffine.Point] : L 1 ≠ 0 := by
  intro h
  have h1 : (1 : ℕ∞) ≤ mordellWeilRank (W.map (Int.castRingHom ℚ)) :=
    ((BSD_statement hBSD W L hW hL).2).1 h
  rw [mordellWeilRank_eq_zero_of_finite] at h1
  exact absurd h1 (by simp)

end Frontier

