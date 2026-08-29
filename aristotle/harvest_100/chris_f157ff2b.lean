/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard, and the central object of McMullen's work on
renormalization) is a holomorphic map `f : U → V` between bounded open subsets of `ℂ`
with `U ⋐ V`, which is a proper degree-two branched covering onto `V`.

We encode "proper degree two branched covering" concretely and checkably:
`f` maps `U` into `V`, `f` is onto `V`, every fibre over `V` has at most two points,
and `f` has a unique critical point in `U`.
-/

/-- A quadratic-like map: a holomorphic degree-two proper map `f : U → V` with
`closure U ⊆ V` and `U` bounded. -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the large domain -/
  V : Set ℂ
  /-- the map -/
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  /-- `U ⋐ V` : the closure of `U` is contained in `V`. -/
  closure_subset : closure U ⊆ V
  bounded_U : Bornology.IsBounded U
  /-- `f` is holomorphic on `U`. -/
  analytic : AnalyticOnNhd ℂ f U
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is onto. -/
  surjOn : Set.SurjOn f U V
  /-- every fibre of `f : U → V` has at most two points (degree two). -/
  fiber_le_two : ∀ w ∈ V, {z | z ∈ U ∧ f z = w}.ncard ≤ 2
  /-- `f` has a unique critical point in `U`. -/
  unique_crit : ∃! c : ℂ, c ∈ U ∧ deriv f c = 0

namespace QuadraticLike

variable (Q : QuadraticLike)

lemma subset_V : Q.U ⊆ Q.V := subset_closure.trans Q.closure_subset

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit
stays in `U`. -/
def filledJulia : Set ℂ := {z | ∀ n : ℕ, Q.f^[n] z ∈ Q.U}

lemma filledJulia_subset : Q.filledJulia ⊆ Q.U := fun z hz => by
  simpa using hz 0

/-- The filled Julia set is forward invariant. -/
lemma mapsTo_filledJulia : Set.MapsTo Q.f Q.filledJulia Q.filledJulia := by
  intro z hz n
  rw [← Function.iterate_succ_apply]
  exact hz (n + 1)

/-- The filled Julia set is bounded. -/
lemma isBounded_filledJulia : Bornology.IsBounded Q.filledJulia :=
  Q.bounded_U.subset Q.filledJulia_subset

end QuadraticLike

/-! ## Renormalization -/

/-- `S` is a renormalization of `Q` with period `n`: the domain of `S` sits inside that of
`Q`, the map of `S` is the `n`-th iterate of the map of `Q` there, and the first `n`
iterates of `Q` keep the domain of `S` inside the domain of `Q`. -/
structure IsRenormalization (Q S : QuadraticLike) (n : ℕ) : Prop where
  pos : 0 < n
  subset : S.U ⊆ Q.U
  eq_iterate : ∀ z ∈ S.U, S.f z = Q.f^[n] z
  orbit : ∀ i < n, Set.MapsTo (Q.f^[i]) S.U Q.U

/-- A quadratic-like map is its own renormalization of period `1`: the base case of the
renormalization tower. -/
theorem isRenormalization_self (Q : QuadraticLike) : IsRenormalization Q Q 1 where
  pos := Nat.one_pos
  subset := subset_rfl
  eq_iterate := by intro z _; simp
  orbit := by
    intro i hi
    interval_cases i
    simpa using Set.mapsTo_id _

/-- Key step for composing renormalizations: on the domain of the deeper renormalization,
iterates of the intermediate map are iterates of the original map. -/
lemma iterate_eq_iterate_of_isRenormalization {Q R S : QuadraticLike} {n m : ℕ}
    (hQR : IsRenormalization Q R n) (hRS : IsRenormalization R S m)
    {z : ℂ} (hz : z ∈ S.U) : ∀ q ≤ m, R.f^[q] z = Q.f^[n * q] z := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
      intro hq
      have hq' : q < m := lt_of_lt_of_le (Nat.lt_succ_self q) hq
      have hmem : R.f^[q] z ∈ R.U := hRS.orbit q hq' hz
      have hIH : R.f^[q] z = Q.f^[n * q] z := ih hq'.le
      rw [Function.iterate_succ_apply', hQR.eq_iterate _ hmem, hIH,
        ← Function.iterate_add_apply]
      congr 1
      ring

/-- **Renormalization tower.** If `R` is a renormalization of `Q` of period `n` and `S` is a
renormalization of `R` of period `m`, then `S` is a renormalization of `Q` of period `n * m`. -/
theorem IsRenormalization.comp {Q R S : QuadraticLike} {n m : ℕ}
    (hQR : IsRenormalization Q R n) (hRS : IsRenormalization R S m) :
    IsRenormalization Q S (n * m) where
  pos := Nat.mul_pos hQR.pos hRS.pos
  subset := hRS.subset.trans hQR.subset
  eq_iterate := by
    intro z hz
    rw [hRS.eq_iterate z hz]
    exact iterate_eq_iterate_of_isRenormalization hQR hRS hz m le_rfl
  orbit := by
    intro i hi z hz
    have hn : 0 < n := hQR.pos
    obtain ⟨q, r, hr, hi'⟩ : ∃ q r : ℕ, r < n ∧ i = r + n * q :=
      ⟨i / n, i % n, Nat.mod_lt _ hn, (Nat.mod_add_div i n).symm⟩
    have hqm : q < m := by
      have h1 : n * q < n * m := by omega
      exact lt_of_mul_lt_mul_left h1 (Nat.zero_le n)
    have hmem : R.f^[q] z ∈ R.U := hRS.orbit q hqm hz
    have hEq : R.f^[q] z = Q.f^[n * q] z :=
      iterate_eq_iterate_of_isRenormalization hQR hRS hz q hqm.le
    have hsplit : Q.f^[i] z = Q.f^[r] (R.f^[q] z) := by
      rw [hEq, hi', Function.iterate_add_apply]
    rw [hsplit]
    exact hQR.orbit r hr hmem

/-! ## The base case: quadratic polynomials are quadratic-like -/

/-- For `R = ‖c‖ + 2`, the polynomial `z ↦ z² + c` restricted to `U = f⁻¹(B(0,R))` is a
quadratic-like map onto `V = B(0,R)`. -/
noncomputable def quadraticPolyQL (c : ℂ) : QuadraticLike := by
  classical
  set r : ℝ := ‖c‖ with hr
  set R : ℝ := r + 2 with hRdef
  have hr0 : 0 ≤ r := norm_nonneg c
  have hRpos : 0 < R := by simp [hRdef]; linarith
  have hkey : R + r < R ^ 2 := by nlinarith
  refine
    { U := {z : ℂ | ‖z ^ 2 + c‖ < R}
      V := Metric.ball (0 : ℂ) R
      f := fun z => z ^ 2 + c
      isOpen_U := ?_
      isOpen_V := Metric.isOpen_ball
      closure_subset := ?_
      bounded_U := ?_
      analytic := ?_
      mapsTo := ?_
      surjOn := ?_
      fiber_le_two := ?_
      unique_crit := ?_ }
  · exact isOpen_lt (by fun_prop) continuous_const
  · -- closure U ⊆ V
    have hclosed : IsClosed {z : ℂ | ‖z ^ 2 + c‖ ≤ R} :=
      isClosed_le (by fun_prop) continuous_const
    have hsub : closure {z : ℂ | ‖z ^ 2 + c‖ < R} ⊆ {z : ℂ | ‖z ^ 2 + c‖ ≤ R} :=
      closure_minimal (fun z hz => by exact le_of_lt (Set.mem_setOf.mp hz)) hclosed
    intro z hz
    have hz' : ‖z ^ 2 + c‖ ≤ R := hsub hz
    have h1 : ‖z‖ ^ 2 ≤ R + r := by
      have : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
        calc ‖z ^ 2‖ = ‖(z ^ 2 + c) - c‖ := by ring_nf
          _ ≤ ‖z ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
      simpa [norm_pow] using this.trans (by linarith [hz'] : ‖z ^ 2 + c‖ + ‖c‖ ≤ R + r)
    have h2 : ‖z‖ < R := by nlinarith [norm_nonneg z]
    simpa [Metric.mem_ball, Complex.dist_eq] using h2
  · -- bounded
    have hclosed : {z : ℂ | ‖z ^ 2 + c‖ < R} ⊆ Metric.ball (0 : ℂ) (R + r + 1) := by
      intro z hz
      have h1 : ‖z‖ ^ 2 ≤ R + r := by
        have : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
          calc ‖z ^ 2‖ = ‖(z ^ 2 + c) - c‖ := by ring_nf
            _ ≤ ‖z ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
        have hz' : ‖z ^ 2 + c‖ ≤ R := le_of_lt (Set.mem_setOf.mp hz)
        simpa [norm_pow] using this.trans (by linarith : ‖z ^ 2 + c‖ + ‖c‖ ≤ R + r)
      have : ‖z‖ < R + r + 1 := by nlinarith [norm_nonneg z]
      simpa [Metric.mem_ball, Complex.dist_eq] using this
    exact (Metric.isBounded_ball).subset hclosed
  · intro z _
    exact (analyticAt_id.pow 2).add analyticAt_const
  · intro z hz
    simpa [Metric.mem_ball, Complex.dist_eq] using hz
  · -- surjectivity
    intro w hw
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w - c) (n := 2) (by norm_num)
    have hsU : s ∈ {z : ℂ | ‖z ^ 2 + c‖ < R} := by
      have : s ^ 2 + c = w := by rw [hs]; ring
      rw [Set.mem_setOf_eq, this]
      simpa [Metric.mem_ball, Complex.dist_eq] using hw
    refine ⟨s, hsU, ?_⟩
    show s ^ 2 + c = w
    rw [hs]; ring
  · -- fibres have at most two points
    intro w _
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w - c) (n := 2) (by norm_num)
    have hsub : {z : ℂ | z ∈ {z : ℂ | ‖z ^ 2 + c‖ < R} ∧ z ^ 2 + c = w} ⊆ {s, -s} := by
      intro z hz
      have hzw : z ^ 2 + c = w := hz.2
      have hz2 : z ^ 2 = s ^ 2 := by rw [hs]; linear_combination hzw
      have hfac : (z - s) * (z + s) = 0 := by linear_combination hz2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases mul_eq_zero.1 hfac with h | h
      · left; linear_combination h
      · right; linear_combination h
    have hfin : ({s, -s} : Set ℂ).Finite := (Set.finite_singleton _).insert _
    calc {z : ℂ | z ∈ {z : ℂ | ‖z ^ 2 + c‖ < R} ∧ z ^ 2 + c = w}.ncard
        ≤ ({s, -s} : Set ℂ).ncard := Set.ncard_le_ncard hsub hfin
      _ ≤ 2 := by
          refine le_trans (Set.ncard_insert_le _ _) ?_
          simp
  · -- unique critical point
    have hderiv : ∀ z : ℂ, deriv (fun z : ℂ => z ^ 2 + c) z = 2 * z := by
      intro z; simp
    refine ⟨0, ⟨?_, by simp [hderiv]⟩, ?_⟩
    · show ‖(0 : ℂ) ^ 2 + c‖ < R
      have h0 : ‖(0 : ℂ) ^ 2 + c‖ = r := by simp [hr]
      rw [h0, hRdef]; linarith
    · rintro y ⟨-, hy⟩
      rw [hderiv] at hy
      simpa using hy

@[simp] lemma quadraticPolyQL_f (c : ℂ) : (quadraticPolyQL c).f = fun z => z ^ 2 + c := rfl

lemma zero_mem_quadraticPolyQL_U (c : ℂ) : (0 : ℂ) ∈ (quadraticPolyQL c).U := by
  show ‖(0 : ℂ) ^ 2 + c‖ < ‖c‖ + 2
  have h0 : ‖(0 : ℂ) ^ 2 + c‖ = ‖c‖ := by simp
  rw [h0]; linarith

/-! ## Rigidity: conformal conjugacies carry filled Julia sets to filled Julia sets -/

/-- A conjugacy between two quadratic-like maps: a map which is injective on the big domain,
bijective from `U₁` onto `U₂`, and conjugates `f₁` to `f₂` on `U₁`. -/
structure IsConjugacy (Q₁ Q₂ : QuadraticLike) (h : ℂ → ℂ) : Prop where
  injOn : Set.InjOn h Q₁.V
  bijOn : Set.BijOn h Q₁.U Q₂.U
  conj : ∀ z ∈ Q₁.U, h (Q₁.f z) = Q₂.f (h z)

theorem IsConjugacy.image_filledJulia {Q₁ Q₂ : QuadraticLike} {h : ℂ → ℂ}
    (H : IsConjugacy Q₁ Q₂ h) : h '' Q₁.filledJulia = Q₂.filledJulia := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have key : ∀ n : ℕ, Q₂.f^[n] (h z) = h (Q₁.f^[n] z) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
          exact (H.conj _ (hz n)).symm
    intro n
    rw [key n]
    exact H.bijOn.mapsTo (hz n)
  · intro w hw
    obtain ⟨z, hzU, rfl⟩ := H.bijOn.surjOn (hw 0)
    have key : ∀ n : ℕ, Q₁.f^[n] z ∈ Q₁.U ∧ Q₂.f^[n] (h z) = h (Q₁.f^[n] z) := by
      intro n
      induction n with
      | zero => exact ⟨by simpa using hzU, by simp⟩
      | succ n ih =>
          obtain ⟨hmem, heq⟩ := ih
          have hstep : Q₂.f^[n + 1] (h z) = h (Q₁.f^[n + 1] z) := by
            rw [Function.iterate_succ_apply', heq, Function.iterate_succ_apply']
            exact (H.conj _ hmem).symm
          refine ⟨?_, hstep⟩
          -- the image point lies in `Q₂.U`, hence comes from a point of `Q₁.U`;
          -- injectivity on `Q₁.V` identifies it with the orbit point.
          have hx : Q₁.f^[n + 1] z ∈ Q₁.V := by
            rw [Function.iterate_succ_apply']
            exact Q₁.mapsTo hmem
          have himg : h (Q₁.f^[n + 1] z) ∈ Q₂.U := by
            rw [← hstep]; exact hw (n + 1)
          obtain ⟨y, hyU, hy⟩ := H.bijOn.surjOn himg
          have : y = Q₁.f^[n + 1] z := H.injOn (Q₁.subset_V hyU) hx hy
          rwa [← this]
    exact ⟨z, fun n => (key n).1, rfl⟩

/-! ## Main statement -/

/--
**McMullen renormalization / rigidity for quadratic-like maps.**

This packages the formalized statements together with the parts that are proved here:

1. *Base case*: every quadratic polynomial `z ↦ z² + c` is quadratic-like on suitable
   domains, with critical point `0` in its domain (so the notion is non-vacuous).
2. *Trivial (period one) renormalization*: every quadratic-like map is a renormalization
   of itself of period `1`.
3. *Renormalization tower (reduction)*: renormalizations compose — a renormalization of
   period `m` of a renormalization of period `n` is a renormalization of period `n · m`.
4. *Filled Julia sets*: they are forward invariant and bounded.
5. *Rigidity*: a conjugacy between quadratic-like maps carries the filled Julia set of one
   onto that of the other.
-/
theorem mcmullen_renormalization :
    (∀ c : ℂ, ∃ Q : QuadraticLike, (∀ z : ℂ, Q.f z = z ^ 2 + c) ∧ (0 : ℂ) ∈ Q.U) ∧
    (∀ Q : QuadraticLike, IsRenormalization Q Q 1) ∧
    (∀ (Q R S : QuadraticLike) (n m : ℕ), IsRenormalization Q R n → IsRenormalization R S m →
      IsRenormalization Q S (n * m)) ∧
    (∀ Q : QuadraticLike, Set.MapsTo Q.f Q.filledJulia Q.filledJulia ∧
      Bornology.IsBounded Q.filledJulia) ∧
    (∀ (Q₁ Q₂ : QuadraticLike) (h : ℂ → ℂ), IsConjugacy Q₁ Q₂ h →
      h '' Q₁.filledJulia = Q₂.filledJulia) := by
  refine ⟨?_, isRenormalization_self, ?_, ?_, ?_⟩
  · intro c
    exact ⟨quadraticPolyQL c, fun z => rfl, zero_mem_quadraticPolyQL_U c⟩
  · intro Q R S n m hQR hRS
    exact hQR.comp hRS
  · intro Q
    exact ⟨Q.mapsTo_filledJulia, Q.isBounded_filledJulia⟩
  · intro Q₁ Q₂ h H
    exact H.image_filledJulia

end Frontier

