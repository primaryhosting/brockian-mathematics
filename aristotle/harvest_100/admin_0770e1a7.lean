import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The argument is the classical Galois-theoretic one: the quintic `X ^ 5 - 4 * X + 2` is
irreducible over `ℚ` (Eisenstein at `2`), has exactly `3` real roots and hence exactly
`2` non-real complex roots, so its Galois group is the full symmetric group on its `5`
complex roots, which is not solvable.  Consequently none of its roots is expressible by
radicals, i.e. the general quintic equation admits no solution formula in radicals.
-/

open Function Polynomial Polynomial.Gal Ideal

namespace AbelRuffiniDeg5

attribute [local instance] splits_ℚ_ℂ

/-- The quintic `X ^ 5 - 4 * X + 2`, over an arbitrary commutative ring. -/
noncomputable def Q (R : Type*) [CommRing R] : Polynomial R :=
  X ^ 5 - C 4 * X + C 2

variable {R : Type*} [CommRing R]

@[simp]
theorem map_Q {S : Type*} [CommRing S] (f : R →+* S) : (Q R).map f = Q S := by
  simp [Q, map_ofNat]

variable (R) in
theorem degree_Q [Nontrivial R] : (Q R).degree = ((5 : ℕ) : WithBot ℕ) := by
  unfold Q
  compute_degree!

variable (R) in
theorem natDegree_Q [Nontrivial R] : (Q R).natDegree = 5 :=
  natDegree_eq_of_degree_eq_some (degree_Q R)

variable (R) in
theorem monic_Q [Nontrivial R] : (Q R).Monic := by
  unfold Q
  monicity!

/-- `X ^ 5 - 4 * X + 2` is irreducible over `ℚ`, by the Eisenstein criterion at the prime `2`. -/
theorem irreducible_Q : Irreducible (Q ℚ) := by
  rw [← map_Q (Int.castRingHom ℚ), ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  on_goal 1 =>
    apply irreducible_of_eisenstein_criterion
    · exact (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr Int.prime_two
    · rw [(monic_Q ℤ).leadingCoeff, mem_span_singleton]
      norm_num
    · intro n hn
      rw [mem_span_singleton]
      rw [degree_Q] at hn
      norm_cast at hn
      interval_cases n <;> simp [Q, coeff_X_pow, coeff_X]
    · simp only [degree_Q, ← WithBot.coe_zero]
      decide
    · rw [span_singleton_pow, mem_span_singleton]
      simp [Q, coeff_X_pow]
  all_goals exact (monic_Q ℤ).isPrimitive

set_option maxHeartbeats 1000000 in
/-- `X ^ 5 - 4 * X + 2` has at most three real roots: two applications of Rolle's theorem
reduce this to the fact that its second derivative `20 * X ^ 3` has a single root. -/
theorem real_roots_Q_le : Fintype.card ((Q ℚ).rootSet ℝ) ≤ 3 := by
  have h : Q ℚ = C 1 * X ^ 5 - C 4 * X + C 2 := by simp [Q]
  rw [h]
  apply (card_rootSet_le_derivative _).trans
    (Nat.succ_le_succ ((card_rootSet_le_derivative _).trans (Nat.succ_le_succ _)))
  suffices (Polynomial.rootSet (C (5 : ℚ) * C 4 * X ^ 3) ℝ).Subsingleton by
    norm_num [Fintype.card_le_one_iff_subsingleton, ← mul_assoc] at *
    exact this
  rw [← C_mul, rootSet_C_mul_X_pow] <;> norm_num

/-- `X ^ 5 - 4 * X + 2` has a root in `(0, 1)` and a root in `(1, 2)`, by the
intermediate value theorem. -/
theorem exists_two_real_roots : ∃ x y : ℝ, x ≠ y ∧ aeval x (Q ℚ) = 0 ∧ aeval y (Q ℚ) = 0 := by
  set f : ℝ → ℝ := fun x : ℝ => aeval x (Q ℚ) with hfdef
  have hf : ∀ x : ℝ, f x = x ^ 5 - 4 * x + 2 := by intro x; simp [hfdef, Q]
  have hc : ∀ s : Set ℝ, ContinuousOn f s := fun s => (Q ℚ).continuousOn_aeval
  have h0 : f 0 = 2 := by rw [hf]; norm_num
  have h1 : f 1 = -1 := by rw [hf]; norm_num
  have h2 : f 2 = 26 := by rw [hf]; norm_num
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1) (hc _)
    (by rw [h0, h1]; norm_num : (0 : ℝ) ∈ Set.Ioo (f 1) (f 0))
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2) (hc _)
    (by rw [h1, h2]; norm_num : (0 : ℝ) ∈ Set.Ioo (f 1) (f 2))
  refine ⟨x, y, ?_, hx0, hy0⟩
  have hx1 := hx.2
  have hy1 := hy.1
  intro h
  subst h
  linarith

theorem real_roots_Q_ge : 2 ≤ Fintype.card ((Q ℚ).rootSet ℝ) := by
  have q_ne_zero : Q ℚ ≠ 0 := (monic_Q ℚ).ne_zero
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_two_real_roots
  have key : ↑({x, y} : Finset ℝ) ⊆ (Q ℚ).rootSet ℝ := by
    simp [Set.insert_subset, mem_rootSet_of_ne q_ne_zero, hx, hy]
  convert Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ key)
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_singleton,
    Finset.card_insert_of_notMem (mt Finset.mem_singleton.mp hxy)]

theorem complex_roots_Q : Fintype.card ((Q ℚ).rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree irreducible_Q.separable (IsAlgClosed.splits _)).trans (natDegree_Q ℚ)

/-- The Galois group of `X ^ 5 - 4 * X + 2` acts on its five complex roots as the full
symmetric group. -/
theorem gal_Q : Bijective (galActionHom (Q ℚ) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' irreducible_Q
  · simp only [natDegree_Q]; decide
  · rw [complex_roots_Q, Nat.succ_le_succ_iff]
    exact real_roots_Q_le.trans (Nat.le_succ 3)
  · simp_rw [complex_roots_Q, Nat.succ_le_succ_iff]
    exact real_roots_Q_ge

/-- The Galois group of `X ^ 5 - 4 * X + 2` is not solvable, since it surjects onto the
symmetric group on five letters. -/
theorem not_solvable_gal_Q : ¬ IsSolvable (Q ℚ).Gal := by
  intro h
  refine Equiv.Perm.not_solvable _ (le_of_eq ?_) (solvable_of_surjective gal_Q.2)
  rw_mod_cast [Cardinal.mk_fintype, complex_roots_Q]

theorem not_solvableByRad (x : ℂ) (hx : aeval x (Q ℚ) = 0) : ¬ IsSolvableByRad ℚ x :=
  fun h => not_solvable_gal_Q (solvableByRad.isSolvable' irreducible_Q hx h)

end AbelRuffiniDeg5

namespace Math

open AbelRuffiniDeg5 in
/-- **Abel–Ruffini theorem in degree 5.** The general quintic equation is not solvable by
radicals: there is a quintic polynomial over `ℚ` (namely `X ^ 5 - 4 * X + 2`) which is
irreducible, whose Galois group is not solvable, and none of whose (existing) complex roots
is expressible by radicals over `ℚ`. -/
theorem abel_ruffini_deg5 :
    ∃ p : Polynomial ℚ, p.natDegree = 5 ∧ Irreducible p ∧ ¬ IsSolvable p.Gal ∧
      (∃ x : ℂ, aeval x p = 0) ∧
      ∀ x : ℂ, aeval x p = 0 → ¬ IsSolvableByRad ℚ x := by
  refine ⟨Q ℚ, natDegree_Q ℚ, irreducible_Q, not_solvable_gal_Q, ?_, not_solvableByRad⟩
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Q ℂ)).exists_eval_eq_zero (by simp [degree_Q])
  rw [← map_Q (algebraMap ℚ ℂ), eval_map] at hx
  exact ⟨x, hx⟩

end Math

#print axioms Math.abel_ruffini_deg5

import Mathlib

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

