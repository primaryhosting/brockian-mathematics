/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Finset MeasureTheory Metric Module Real Set

/-! ## The Pfaffian of the curvature form of the unit round sphere -/

section Pfaffian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- First index of the `i`-th pair `(2i, 2i+1)`. -/
def pairFst (m : ℕ) (i : Fin m) : Fin (2 * m) := ⟨2 * i.1, by have := i.2; omega⟩

/-- Second index of the `i`-th pair `(2i, 2i+1)`. -/
def pairSnd (m : ℕ) (i : Fin m) : Fin (2 * m) := ⟨2 * i.1 + 1, by have := i.2; omega⟩

/-- The curvature two-forms of the unit round sphere `S^{2m}` written in an orthonormal
coframe `v`: `Ω i j = v i ∧ v j`. -/
noncomputable def curvForm {m : ℕ} (v : Fin (2 * m) → V) (i j : Fin (2 * m)) :
    ExteriorAlgebra ℝ V :=
  ExteriorAlgebra.ι ℝ (v i) * ExteriorAlgebra.ι ℝ (v j)

/-- The ordered product `Ω_{01} ∧ Ω_{23} ∧ ⋯ ∧ Ω_{(2m-2)(2m-1)}` of curvature two-forms. -/
noncomputable def pairProd (m : ℕ) (v : Fin (2 * m) → V) : ExteriorAlgebra ℝ V :=
  (List.ofFn fun i : Fin m => curvForm v (pairFst m i) (pairSnd m i)).prod

/-- The Pfaffian of the curvature form of the unit round sphere `S^{2m}`, computed in an
orthonormal coframe `v`:
`Pf(Ω) = (2^m m!)⁻¹ ∑_{σ ∈ S_{2m}} sgn(σ) Ω_{σ(0)σ(1)} ∧ ⋯ ∧ Ω_{σ(2m-2)σ(2m-1)}`. -/
noncomputable def spherePfaffian (m : ℕ) (v : Fin (2 * m) → V) : ExteriorAlgebra ℝ V :=
  ((2 ^ m * (m)! : ℝ))⁻¹ •
    ∑ σ : Equiv.Perm (Fin (2 * m)), (Equiv.Perm.sign σ : ℝ) • pairProd m (v ∘ σ)

theorem prod_range_pairs {M : Type*} [Monoid M] (m : ℕ) (a : ℕ → M) :
    ((List.range m).map (fun i => a (2 * i) * a (2 * i + 1))).prod
      = ((List.range (2 * m)).map a).prod := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [h2, List.range_succ, List.map_append, List.prod_append, List.range_succ,
      List.map_append, List.prod_append]
    simp [mul_assoc]

theorem list_prod_range_eq_ofFn {M : Type*} [Monoid M] (n : ℕ) (a : ℕ → M) :
    ((List.range n).map a).prod = (List.ofFn fun i : Fin n => a i.1).prod := by
  congr 1
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range (n := n), List.map_map]
  rfl

/-- The wedge of the curvature two-forms of the unit sphere along the pairing
`(0,1), (2,3), …` is the full wedge product of the coframe. -/
theorem pairProd_eq_ιMulti (m : ℕ) (v : Fin (2 * m) → V) :
    pairProd m v = ExteriorAlgebra.ιMulti ℝ (2 * m) v := by
  classical
  set A : ℕ → ExteriorAlgebra ℝ V :=
    fun j => if h : j < 2 * m then ExteriorAlgebra.ι ℝ (v ⟨j, h⟩) else 1 with hA
  have hAval : ∀ i : Fin (2 * m), A i.1 = ExteriorAlgebra.ι ℝ (v i) := by
    intro i; simp only [hA, dif_pos i.2]
  have h1 : pairProd m v = ((List.range m).map (fun i => A (2 * i) * A (2 * i + 1))).prod := by
    rw [list_prod_range_eq_ofFn]
    simp only [pairProd, curvForm]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    show _ = A (pairFst m i).1 * A (pairSnd m i).1
    rw [hAval (pairFst m i), hAval (pairSnd m i)]
  rw [h1, prod_range_pairs, list_prod_range_eq_ofFn, ExteriorAlgebra.ιMulti_apply]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => hAval i))

theorem pairProd_perm (m : ℕ) (v : Fin (2 * m) → V) (σ : Equiv.Perm (Fin (2 * m))) :
    pairProd m (v ∘ σ) = (Equiv.Perm.sign σ : ℝ) • ExteriorAlgebra.ιMulti ℝ (2 * m) v := by
  rw [pairProd_eq_ιMulti, AlternatingMap.map_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- **The Pfaffian of the curvature form of the unit round sphere.**
For the round sphere `S^{2m}` of radius one, the curvature two-forms in an orthonormal coframe
`v` are `Ω i j = v i ∧ v j`, and the Pfaffian of `Ω` equals `(2m)! / (2^m m!)` times the
volume form `v 0 ∧ ⋯ ∧ v (2m-1)`. -/
theorem spherePfaffian_eq (m : ℕ) (v : Fin (2 * m) → V) :
    spherePfaffian m v = ((2 * m)! / (2 ^ m * (m)!) : ℝ) • ExteriorAlgebra.ιMulti ℝ (2 * m) v := by
  have hterm : ∀ σ : Equiv.Perm (Fin (2 * m)),
      (Equiv.Perm.sign σ : ℝ) • pairProd m (v ∘ σ) = ExteriorAlgebra.ιMulti ℝ (2 * m) v := by
    intro σ
    rw [pairProd_perm, smul_smul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [spherePfaffian, Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  field_simp

end Pfaffian

/-! ## The total surface measure of the round sphere `S^{2m}` -/

/-- The `2m`-dimensional surface measure of the unit sphere `S^{2m} ⊆ ℝ^{2m+1}`, obtained from
the Lebesgue measure by the polar coordinate decomposition. -/
noncomputable def sphereArea (m : ℕ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin (2 * m + 1)))).toSphere.real Set.univ

theorem sphereArea_eq_doubleFactorial (m : ℕ) :
    sphereArea m = (2 * m + 1) * (π ^ m * 2 ^ (m + 1) / ((2 * m + 1)‼ : ℕ)) := by
  rw [sphereArea, Measure.toSphere_real_apply_univ]
  have hrank : finrank ℝ (EuclideanSpace ℝ (Fin (2 * m + 1))) = 2 * m + 1 := by simp
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_odd (k := m) (by simp) 0 1, hrank]
  have hpos : (0 : ℝ) ≤ π ^ m * 2 ^ (m + 1) / ((2 * m + 1)‼ : ℕ) := by positivity
  rw [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal hpos]
  push_cast
  ring

theorem doubleFactorial_mul (m : ℕ) : (2 * m + 1)‼ * (2 ^ m * (m)!) = (2 * m + 1)! := by
  rw [Nat.factorial_eq_mul_doubleFactorial (2 * m), Nat.doubleFactorial_two_mul]

/-- The total surface measure of the unit sphere `S^{2m} ⊆ ℝ^{2m+1}` is
`2^{2m+1} π^m m! / (2m)!`. -/
theorem sphereArea_eq (m : ℕ) :
    sphereArea m = 2 ^ (2 * m + 1) * π ^ m * (m)! / (2 * m)! := by
  have hcast : ((2 * m + 1)‼ : ℝ) * (2 ^ m * (m)!) = (2 * m + 1) * ((2 * m)! : ℕ) := by
    have h : ((2 * m + 1)‼ * (2 ^ m * (m)!) : ℕ) = ((2 * m + 1) * (2 * m)! : ℕ) := by
      rw [doubleFactorial_mul, Nat.factorial_succ]
    exact_mod_cast h
  rw [sphereArea_eq_doubleFactorial, mul_div_assoc',
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(π ^ m * 2 ^ (m + 1))) * hcast

/-! ## The Euler characteristic of a simplicial `2m`-sphere -/

/-- The Euler characteristic of the boundary complex of the `(2m+1)`-simplex, a triangulation
of the `2m`-sphere: the alternating sum of the numbers of `k`-dimensional faces. -/
def simplicialSphereEulerChar (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (2 * m + 1), (-1) ^ k * ((2 * m + 2).choose (k + 1) : ℤ)

theorem simplicialSphereEulerChar_eq (m : ℕ) : simplicialSphereEulerChar m = 2 := by
  have h := Int.alternating_sum_range_choose (n := 2 * m + 2)
  rw [Finset.sum_range_succ', Finset.sum_range_succ] at h
  simp only [Nat.choose_zero_right, Nat.choose_self, pow_succ, pow_mul, Nat.cast_one, mul_one,
    if_neg (by omega : ¬(2 * m + 2 = 0))] at h
  have hneg : ∑ x ∈ Finset.range (2 * m + 1), (-1 : ℤ) ^ x * -1 * ((2 * m + 2).choose (x + 1) : ℤ)
      = -∑ k ∈ Finset.range (2 * m + 1), (-1 : ℤ) ^ k * ((2 * m + 2).choose (k + 1) : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hneg] at h
  norm_num at h
  simp only [simplicialSphereEulerChar]
  linarith

/-! ## Chern–Gauss–Bonnet for the round spheres -/

/-- **The Chern–Gauss–Bonnet theorem for the even-dimensional round spheres.**

For the closed even-dimensional manifold `S^{2m}` with its round metric of constant curvature
one, the Euler form is `(2π)^{-m} Pf(Ω)`; by `Math2.spherePfaffian_eq` its density with respect
to the Riemannian volume is the constant `(2m)!/(2^m m!) / (2π)^m`.  The theorem states that the
integral of the Euler form over `S^{2m}` — that constant times the total surface measure
`Math2.sphereArea m` — equals the Euler characteristic of `S^{2m}`, computed here as the Euler
characteristic of its triangulation by the boundary of the `(2m+1)`-simplex. -/
theorem chern_gauss_bonnet (m : ℕ) :
    (1 / (2 * π) ^ m) * ((2 * m)! / (2 ^ m * (m)!) : ℝ) * sphereArea m
      = (simplicialSphereEulerChar m : ℝ) := by
  rw [sphereArea_eq, simplicialSphereEulerChar_eq]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hm : ((m)! : ℝ) ≠ 0 := by positivity
  have h2m : (((2 * m)! : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- A restatement of `Math2.chern_gauss_bonnet` directly in terms of the Pfaffian of the
curvature form: if `c` is the density of the Pfaffian `Pf(Ω)` of the curvature form of the unit
round sphere `S^{2m}` with respect to the volume form of a coframe `v` spanning a nonzero
volume element, then `(2π)^{-m} c` integrated over `S^{2m}` is the Euler characteristic. -/
theorem chern_gauss_bonnet_pfaffian (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : Fin (2 * m) → V) (c : ℝ)
    (hv : ExteriorAlgebra.ιMulti ℝ (2 * m) v ≠ 0)
    (hc : spherePfaffian m v = c • ExteriorAlgebra.ιMulti ℝ (2 * m) v) :
    (1 / (2 * π) ^ m) * c * sphereArea m = (simplicialSphereEulerChar m : ℝ) := by
  have hcval : c = ((2 * m)! / (2 ^ m * (m)!) : ℝ) := by
    by_contra hne
    apply hv
    have hzero : (c - ((2 * m)! / (2 ^ m * (m)!) : ℝ)) • ExteriorAlgebra.ιMulti ℝ (2 * m) v = 0 := by
      rw [sub_smul, ← hc, spherePfaffian_eq, sub_self]
    rcases smul_eq_zero.mp hzero with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hne
    · exact h1
  rw [hcval]
  exact chern_gauss_bonnet m

end Math2

