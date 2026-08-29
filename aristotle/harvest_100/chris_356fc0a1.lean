/-
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module docstring before `import`; the required header is repeated verbatim
-- as the module docstring immediately below the import.)

import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open scoped TensorProduct

/-! ## The arithmetic side: Mordell–Weil rank -/

/-- The Mordell–Weil group `E(ℚ)` of an integral Weierstrass model `W`, i.e. the group of
rational nonsingular points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The Mordell–Weil rank of `E(ℚ)`, defined as the dimension of `ℚ ⊗ℤ E(ℚ)` over `ℚ`.
For a finitely generated abelian group this is exactly the rank of its free part. -/
noncomputable def mwRank (W : WeierstrassCurve ℤ) : ℕ :=
  Module.finrank ℚ (ℚ ⊗[ℤ] MordellWeil W)

/-! ## The analytic side: the Hasse–Weil `L`-function -/

/-- The number of nonsingular points of the reduction of the integral Weierstrass model `W`
modulo `p`, including the point at infinity. -/
noncomputable def pointCountModP (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card (W.baseChange (ZMod p)).toAffine.Point

/-- `W` has good reduction at `p` when `p` does not divide the discriminant of `W`.
(For a global minimal model this is the usual notion of good reduction.) -/
abbrev HasGoodReductionAt (W : WeierstrassCurve ℤ) (p : ℕ) : Prop := ¬ p ∣ W.Δ.natAbs

/-- The `p`-th coefficient of the Hasse–Weil `L`-function. At a prime of good reduction this is
the trace of Frobenius `a_p = p + 1 - #E(𝔽_p)`. At a prime of bad reduction it is
`a_p = p - #E_ns(𝔽_p)`, which is `1`, `-1`, `0` according to whether the reduction is split
multiplicative, nonsplit multiplicative, or additive. -/
noncomputable def apCoeff (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (if HasGoodReductionAt W p then (p : ℤ) + 1 else (p : ℤ)) - (pointCountModP W p : ℤ)

/-- The local Euler factor of `W` at the prime `p`:
`(1 - a_p p^{-s} + p^{1-2s})⁻¹` at primes of good reduction and `(1 - a_p p^{-s})⁻¹` at primes
of bad reduction (where `a_p ∈ {0, ±1}` records the type of bad reduction). -/
noncomputable def eulerFactor (W : WeierstrassCurve ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - (apCoeff W p : ℂ) * (p : ℂ) ^ (-s)
      + (if HasGoodReductionAt W p then 1 else 0) * (p : ℂ) ^ (1 - 2 * s))⁻¹

/-- The half-plane of absolute convergence `Re s > 3/2` of the Hasse–Weil Euler product. -/
def convergenceHalfPlane : Set ℂ := {s : ℂ | 3 / 2 < s.re}

/-- `L` is *the* Hasse–Weil `L`-function of the integral Weierstrass model `W`: it is entire
(this is the content of the modularity theorem) and on the half-plane `Re s > 3/2` it is given
by the Euler product `∏_p (1 - a_p p^{-s} + ε_p p^{1-2s})⁻¹`. -/
structure IsHasseWeilL (W : WeierstrassCurve ℤ) (L : ℂ → ℂ) : Prop where
  /-- `L` is entire, i.e. analytic at every point of `ℂ`. -/
  entire : ∀ s : ℂ, AnalyticAt ℂ L s
  /-- On `Re s > 3/2`, `L s` is the value of the Hasse–Weil Euler product. -/
  hasProd : ∀ s ∈ convergenceHalfPlane, HasProd (fun p : Nat.Primes => eulerFactor W p s) (L s)

/-- `W` is a global minimal Weierstrass model of the elliptic curve it defines over `ℚ`:
among all integral models of the same curve it has discriminant of least absolute value. -/
def IsGlobalMinimalModel (W : WeierstrassCurve ℤ) : Prop :=
  ∀ W' : WeierstrassCurve ℤ, W'.baseChange ℚ = W.baseChange ℚ → W.Δ.natAbs ≤ W'.Δ.natAbs

/-! ## The Birch and Swinnerton-Dyer conjecture -/

/-- **The Birch and Swinnerton-Dyer conjecture (rank part).**
For every elliptic curve `E/ℚ`, given by a global minimal integral Weierstrass model `W`, the
order of vanishing at `s = 1` of the Hasse–Weil `L`-function of `E` equals the rank of the
Mordell–Weil group `E(ℚ)`:
`ord_{s=1} L(E, s) = rank E(ℚ)`. -/
def BSD_statement : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (L : ℂ → ℂ), (W.baseChange ℚ).IsElliptic → IsGlobalMinimalModel W →
    IsHasseWeilL W L → analyticOrderAt L 1 = (mwRank W : ℕ∞)

/-! ## Well-posedness: the `L`-function is unique -/

theorem isOpen_convergenceHalfPlane : IsOpen convergenceHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem two_mem_convergenceHalfPlane : (2 : ℂ) ∈ convergenceHalfPlane := by
  norm_num [convergenceHalfPlane]

/-- The Hasse–Weil `L`-function of `W`, if it exists, is unique: this is the identity principle
applied to two entire functions agreeing on the half-plane of convergence. Hence
`Frontier.BSD_statement` is a well-posed assertion about `E`. -/
theorem hasseWeilL_unique {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsHasseWeilL W L₁) (h₂ : IsHasseWeilL W L₂) : L₁ = L₂ := by
  have heq : Set.EqOn L₁ L₂ convergenceHalfPlane := fun s hs =>
    (h₁.hasProd s hs).unique (h₂.hasProd s hs)
  have hev : L₁ =ᶠ[nhds (2 : ℂ)] L₂ :=
    Filter.eventuallyEq_of_mem
      (isOpen_convergenceHalfPlane.mem_nhds two_mem_convergenceHalfPlane) heq
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun s _ => h₁.entire s) (fun s _ => h₂.entire s) hev

/-! ## A base case: curves with torsion Mordell–Weil group -/

/-- If `M` is a torsion abelian group then `ℚ ⊗ℤ M` vanishes. -/
theorem subsingleton_rat_tensor_of_isTorsion (M : Type) [AddCommGroup M]
    (h : AddMonoid.IsTorsion M) : Subsingleton (ℚ ⊗[ℤ] M) := by
  constructor
  have key : ∀ x : ℚ ⊗[ℤ] M, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul q m =>
        obtain ⟨n, hn, hnm⟩ : ∃ n : ℕ, 0 < n ∧ (n : ℤ) • m = 0 := by
          refine ⟨addOrderOf m, ?_, ?_⟩
          · exact (h m).addOrderOf_pos
          · simp
        have hq : q = (n : ℤ) • (q / (n : ℚ)) := by
          have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
          rw [zsmul_eq_mul]
          push_cast
          field_simp
        calc q ⊗ₜ[ℤ] m = ((n : ℤ) • (q / (n : ℚ))) ⊗ₜ[ℤ] m := by rw [← hq]
          _ = (q / (n : ℚ)) ⊗ₜ[ℤ] ((n : ℤ) • m) := TensorProduct.smul_tmul _ _ _
          _ = 0 := by rw [hnm, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  intro a b
  rw [key a, key b]

/-- **Base case of BSD (arithmetic side).** If the Mordell–Weil group `E(ℚ)` is torsion — that is,
`E` has rank `0` in the naive sense that every rational point has finite order — then the
Mordell–Weil rank as defined above is `0`. -/
theorem mwRank_eq_zero_of_isTorsion {W : WeierstrassCurve ℤ}
    (h : AddMonoid.IsTorsion (MordellWeil W)) : mwRank W = 0 := by
  have : Subsingleton (ℚ ⊗[ℤ] MordellWeil W) := subsingleton_rat_tensor_of_isTorsion _ h
  simp [mwRank, Module.finrank_zero_of_subsingleton]

/-! ## Lean-checked reductions of BSD -/

/-- **Reduction of BSD to a nonvanishing statement in rank 0.** Assuming BSD, an elliptic curve
whose rational points are all torsion has nonvanishing `L`-value at `s = 1`. This is the base case
`rank = 0 ⟹ L(E, 1) ≠ 0` of the conjecture. -/
theorem BSD_base_case_rank_zero (hBSD : BSD_statement) {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hE : (W.baseChange ℚ).IsElliptic) (hmin : IsGlobalMinimalModel W) (hL : IsHasseWeilL W L)
    (htors : AddMonoid.IsTorsion (MordellWeil W)) : L 1 ≠ 0 := by
  have h := hBSD W L hE hmin hL
  rw [mwRank_eq_zero_of_isTorsion htors] at h
  simpa using ((hL.entire 1).analyticOrderAt_eq_zero).mp (by simpa using h)

/-- **Weak BSD, as a consequence of BSD.** Assuming BSD, the Mordell–Weil rank vanishes exactly
when the `L`-function does not vanish at `s = 1`. -/
theorem BSD_rank_zero_iff (hBSD : BSD_statement) {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hE : (W.baseChange ℚ).IsElliptic) (hmin : IsGlobalMinimalModel W) (hL : IsHasseWeilL W L) :
    mwRank W = 0 ↔ L 1 ≠ 0 := by
  have h := hBSD W L hE hmin hL
  rw [← (hL.entire 1).analyticOrderAt_eq_zero, h]
  simp

/-- **Assuming BSD, positive rank forces vanishing of the `L`-value.** -/
theorem BSD_L_eq_zero_of_pos_rank (hBSD : BSD_statement) {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hE : (W.baseChange ℚ).IsElliptic) (hmin : IsGlobalMinimalModel W) (hL : IsHasseWeilL W L)
    (hr : 0 < mwRank W) : L 1 = 0 := by
  by_contra hne
  exact absurd ((BSD_rank_zero_iff hBSD hE hmin hL).mpr hne) hr.ne'

/-- **Assuming BSD, the analytic rank is finite**, i.e. the `L`-function of an elliptic curve is
not identically zero near `s = 1`. -/
theorem BSD_analyticOrder_ne_top (hBSD : BSD_statement) {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hE : (W.baseChange ℚ).IsElliptic) (hmin : IsGlobalMinimalModel W) (hL : IsHasseWeilL W L) :
    analyticOrderAt L 1 ≠ ⊤ := by
  rw [hBSD W L hE hmin hL]
  exact ENat.coe_ne_top _

/-- **Assuming BSD, the `L`-function of an elliptic curve is not identically zero.** -/
theorem BSD_L_ne_zero (hBSD : BSD_statement) {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hE : (W.baseChange ℚ).IsElliptic) (hmin : IsGlobalMinimalModel W) (hL : IsHasseWeilL W L) :
    L ≠ 0 := by
  intro h
  refine BSD_analyticOrder_ne_top hBSD hE hmin hL ?_
  rw [analyticOrderAt_eq_top]
  filter_upwards with z
  rw [h]
  rfl

/-- **Reduction of BSD to two inequalities.** BSD holds if and only if, for every elliptic curve
over `ℚ` with global minimal model `W` and Hasse–Weil `L`-function `L`, the analytic rank is at
most the algebraic rank and the algebraic rank is at most the analytic rank. -/
theorem BSD_iff_two_inequalities :
    BSD_statement ↔
      (∀ (W : WeierstrassCurve ℤ) (L : ℂ → ℂ), (W.baseChange ℚ).IsElliptic →
        IsGlobalMinimalModel W → IsHasseWeilL W L → analyticOrderAt L 1 ≤ (mwRank W : ℕ∞)) ∧
      (∀ (W : WeierstrassCurve ℤ) (L : ℂ → ℂ), (W.baseChange ℚ).IsElliptic →
        IsGlobalMinimalModel W → IsHasseWeilL W L → (mwRank W : ℕ∞) ≤ analyticOrderAt L 1) := by
  constructor
  · intro h
    exact ⟨fun W L hE hmin hL => (h W L hE hmin hL).le,
      fun W L hE hmin hL => (h W L hE hmin hL).ge⟩
  · rintro ⟨h₁, h₂⟩ W L hE hmin hL
    exact le_antisymm (h₁ W L hE hmin hL) (h₂ W L hE hmin hL)

/-- **Contrapositive form of BSD.** BSD fails exactly when some elliptic curve over `ℚ`, given by
a global minimal model with Hasse–Weil `L`-function `L`, has analytic rank different from its
Mordell–Weil rank. -/
theorem not_BSD_iff :
    ¬ BSD_statement ↔
      ∃ (W : WeierstrassCurve ℤ) (L : ℂ → ℂ), (W.baseChange ℚ).IsElliptic ∧
        IsGlobalMinimalModel W ∧ IsHasseWeilL W L ∧ analyticOrderAt L 1 ≠ (mwRank W : ℕ∞) := by
  unfold BSD_statement
  push_neg
  constructor
  · rintro ⟨W, L, hE, hmin, hL, hne⟩
    exact ⟨W, L, hE, hmin, hL, hne⟩
  · rintro ⟨W, L, hE, hmin, hL, hne⟩
    exact ⟨W, L, hE, hmin, hL, hne⟩

end Frontier

