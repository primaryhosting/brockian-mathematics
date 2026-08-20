/- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`, so the
requested header is reproduced verbatim as a block comment here, and again as the module
docstring immediately after the import.)

# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

/-!
The development below is adapted from the Mathlib archive file
`Archive/Wiedijk100Theorems/AbelRuffini.lean` (Thomas Browning, Apache 2.0), which is not
importable from this project, and follows the classical Galois-theoretic proof of the Abel–Ruffini
theorem in degree five: the quintic `Φ a b = X ^ 5 - a * X + b` is irreducible over `ℚ`
by Eisenstein's criterion (for suitable `a`, `b`), has exactly three real roots and two
non-real roots, hence its Galois group is the full symmetric group `S₅`, which is not
solvable.  Consequently no root of this quintic is expressible by radicals.
-/

namespace Math

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- The quintic polynomial `X ^ 5 - a * X + b`. -/
noncomputable def quinticPhi : R[X] :=
  X ^ 5 - C (a : R) * X + C (b : R)

variable {R}

@[simp]
theorem map_quinticPhi {S : Type*} [CommRing S] (f : R →+* S) :
    (quinticPhi R a b).map f = quinticPhi S a b := by simp [quinticPhi]

@[simp]
theorem coeff_zero_quinticPhi : (quinticPhi R a b).coeff 0 = (b : R) := by
  simp [quinticPhi, coeff_X_pow]

@[simp]
theorem coeff_five_quinticPhi : (quinticPhi R a b).coeff 5 = 1 := by
  simp [quinticPhi, -map_natCast]

variable [Nontrivial R]

theorem degree_quinticPhi : (quinticPhi R a b).degree = ((5 : ℕ) : WithBot ℕ) := by
  suffices degree (X ^ 5 - C (a : R) * X) = ((5 : ℕ) : WithBot ℕ) by
    rwa [quinticPhi, degree_add_eq_left_of_degree_lt]
    convert (degree_C_le (R := R)).trans_lt (WithBot.coe_lt_coe.mpr (show 0 < 5 by simp))
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact (degree_C_mul_X_le (a : R)).trans_lt (WithBot.coe_lt_coe.mpr (show 1 < 5 by simp))

theorem natDegree_quinticPhi : (quinticPhi R a b).natDegree = 5 :=
  natDegree_eq_of_degree_eq_some (degree_quinticPhi a b)

theorem leadingCoeff_quinticPhi : (quinticPhi R a b).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, natDegree_quinticPhi, coeff_five_quinticPhi]

theorem monic_quinticPhi : (quinticPhi R a b).Monic :=
  leadingCoeff_quinticPhi a b

theorem irreducible_quinticPhi (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b)
    (hp2b : ¬p ^ 2 ∣ b) : Irreducible (quinticPhi ℚ a b) := by
  rw [← map_quinticPhi a b (Int.castRingHom ℚ),
    ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  on_goal 1 =>
    apply irreducible_of_eisenstein_criterion
    · rwa [span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero), Int.prime_iff_natAbs_prime]
    · rw [leadingCoeff_quinticPhi, mem_span_singleton]
      exact mod_cast mt Nat.dvd_one.mp hp.ne_one
    · intro n hn
      rw [mem_span_singleton]
      rw [degree_quinticPhi] at hn; norm_cast at hn
      interval_cases n <;>
      simp +decide only [quinticPhi, coeff_X_pow, coeff_C, Int.natCast_dvd_natCast.mpr,
        hpb, if_true, coeff_C_mul, if_false, coeff_X_zero, hpa, coeff_add, zero_add, mul_zero,
        coeff_sub, add_zero, zero_sub, dvd_neg, neg_zero, dvd_mul_of_dvd_left]
    · simp only [degree_quinticPhi, ← WithBot.coe_zero]
      decide
    · rw [coeff_zero_quinticPhi, span_singleton_pow, mem_span_singleton]
      exact mt Int.natCast_dvd_natCast.mp hp2b
  all_goals exact Monic.isPrimitive (monic_quinticPhi a b)

attribute [local simp] map_ofNat in -- use `ofNat` simp theorem with bad keys
theorem real_roots_quinticPhi_le : Fintype.card ((quinticPhi ℚ a b).rootSet ℝ) ≤ 3 := by
  rw [← map_quinticPhi a b (algebraMap ℤ ℚ), quinticPhi, ← one_mul (X ^ 5), ← C_1]
  apply (card_rootSet_le_derivative _).trans
    (Nat.succ_le_succ ((card_rootSet_le_derivative _).trans (Nat.succ_le_succ _)))
  suffices (Polynomial.rootSet (C (20 : ℚ) * X ^ 3) ℝ).Subsingleton by
    norm_num [Fintype.card_le_one_iff_subsingleton, ← mul_assoc] at *
    exact this
  rw [rootSet_C_mul_X_pow] <;>
  norm_num

theorem real_roots_quinticPhi_ge_aux (hab : b < a) :
    ∃ x y : ℝ, x ≠ y ∧ aeval x (quinticPhi ℚ a b) = 0 ∧ aeval y (quinticPhi ℚ a b) = 0 := by
  let f : ℝ → ℝ := fun x : ℝ => aeval x (quinticPhi ℚ a b)
  have hf : f = fun x : ℝ => x ^ 5 - a * x + b := by simp [f, quinticPhi]
  have hc : ∀ s : Set ℝ, ContinuousOn f s := fun s => (quinticPhi ℚ a b).continuousOn_aeval
  have ha : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr (Nat.one_le_of_lt hab)
  have hle : (0 : ℝ) ≤ 1 := zero_le_one
  have hf0 : 0 ≤ f 0 := by simp [hf]
  by_cases hb : (1 : ℝ) - a + b < 0
  · have hf1 : f 1 < 0 := by simp [hf, hb]
    have hfa : 0 ≤ f a := by
      simp_rw [hf, ← sq]
      refine add_nonneg (sub_nonneg.mpr (pow_right_mono₀ ha ?_)) ?_ <;> norm_num
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Ico' hle (hc _) (Set.mem_Ioc.mpr ⟨hf1, hf0⟩)
    obtain ⟨y, ⟨hy1, -⟩, hy2⟩ := intermediate_value_Ioc ha (hc _) (Set.mem_Ioc.mpr ⟨hf1, hfa⟩)
    exact ⟨x, y, (hx1.trans hy1).ne, hx2, hy2⟩
  · replace hb : (b : ℝ) = a - 1 := by linarith [show (b : ℝ) + 1 ≤ a from mod_cast hab]
    have hf1 : f 1 = 0 := by simp [hf, hb]
    have hfa :=
      calc
        f (-a) = (a : ℝ) ^ 2 - (a : ℝ) ^ 5 + b := by
          norm_num [hf, ← sq, sub_eq_add_neg, add_comm, Odd.neg_pow (by decide : Odd 5)]
        _ ≤ (a : ℝ) ^ 2 - (a : ℝ) ^ 3 + (a - 1) := by gcongr <;> linarith
        _ = -((a : ℝ) - 1) ^ 2 * (a + 1) := by ring
        _ ≤ 0 := by nlinarith
    have ha' := neg_nonpos.mpr (hle.trans ha)
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Icc ha' (hc _) (Set.mem_Icc.mpr ⟨hfa, hf0⟩)
    exact ⟨x, 1, (hx1.trans_lt zero_lt_one).ne, hx2, hf1⟩

theorem real_roots_quinticPhi_ge (hab : b < a) :
    2 ≤ Fintype.card ((quinticPhi ℚ a b).rootSet ℝ) := by
  have q_ne_zero : quinticPhi ℚ a b ≠ 0 := (monic_quinticPhi a b).ne_zero
  obtain ⟨x, y, hxy, hx, hy⟩ := real_roots_quinticPhi_ge_aux a b hab
  have key : ↑({x, y} : Finset ℝ) ⊆ (quinticPhi ℚ a b).rootSet ℝ := by
    simp [Set.insert_subset, mem_rootSet_of_ne q_ne_zero, hx, hy]
  convert Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ key)
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_singleton,
    Finset.card_insert_of_notMem (mt Finset.mem_singleton.mp hxy)]

theorem complex_roots_quinticPhi (h : (quinticPhi ℚ a b).Separable) :
    Fintype.card ((quinticPhi ℚ a b).rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree h (IsAlgClosed.splits _)).trans (natDegree_quinticPhi a b)

theorem gal_quinticPhi (hab : b < a) (h_irred : Irreducible (quinticPhi ℚ a b)) :
    Bijective (galActionHom (quinticPhi ℚ a b) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' h_irred
  · simp only [natDegree_quinticPhi]; decide
  · rw [complex_roots_quinticPhi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact (real_roots_quinticPhi_le a b).trans (Nat.le_succ 3)
  · simp_rw [complex_roots_quinticPhi a b h_irred.separable, Nat.succ_le_succ_iff]
    exact real_roots_quinticPhi_ge a b hab

/-- The Galois group of the quintic `X ^ 5 - a * X + b` (for suitable `a`, `b`) is not
solvable: it is the full symmetric group on the five complex roots. -/
theorem not_solvable_gal_quinticPhi (p : ℕ) (hab : b < a) (hp : p.Prime) (hpa : p ∣ a)
    (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) : ¬ IsSolvable (quinticPhi ℚ a b).Gal := by
  have h_irred := irreducible_quinticPhi a b p hp hpa hpb hp2b
  intro h
  refine Equiv.Perm.not_solvable _ (le_of_eq ?_)
    (solvable_of_surjective (gal_quinticPhi a b hab h_irred).2)
  rw_mod_cast [Cardinal.mk_fintype, complex_roots_quinticPhi a b h_irred.separable]

theorem not_solvable_by_rad_quinticPhi (p : ℕ) (x : ℂ) (hx : aeval x (quinticPhi ℚ a b) = 0)
    (hab : b < a) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) :
    ¬IsSolvableByRad ℚ x := by
  have h_irred := irreducible_quinticPhi a b p hp hpa hpb hp2b
  exact mt (solvableByRad.isSolvable' h_irred hx)
    (not_solvable_gal_quinticPhi a b p hab hp hpa hpb hp2b)

/-- **Abel–Ruffini in degree 5**: there is a monic irreducible quintic over `ℚ` whose Galois
group is not solvable, so that none of its (complex) roots is expressible by radicals; in
particular the general quintic equation is not solvable by radicals. -/
theorem abel_ruffini_deg5 :
    ∃ p : ℚ[X], p.Monic ∧ p.natDegree = 5 ∧ Irreducible p ∧ ¬ IsSolvable p.Gal ∧
      (∃ x : ℂ, aeval x p = 0) ∧
      ∀ x : ℂ, aeval x p = 0 → IsAlgebraic ℚ x ∧ ¬ IsSolvableByRad ℚ x := by
  refine ⟨quinticPhi ℚ 4 2, monic_quinticPhi 4 2, natDegree_quinticPhi 4 2,
    irreducible_quinticPhi 4 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    not_solvable_gal_quinticPhi 4 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), ?_, ?_⟩
  · obtain ⟨x, hx⟩ :=
      (IsAlgClosed.splits (quinticPhi ℂ 4 2)).exists_eval_eq_zero (by simp [degree_quinticPhi])
    rw [← map_quinticPhi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
    exact ⟨x, hx⟩
  · intro x hx
    exact ⟨⟨quinticPhi ℚ 4 2, (monic_quinticPhi 4 2).ne_zero, hx⟩,
      not_solvable_by_rad_quinticPhi 4 2 2 x hx (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)⟩

end Math

