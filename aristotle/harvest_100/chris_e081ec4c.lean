import RequestProject.Main

/-!
# Log-concavity of the characteristic polynomial of a uniform matroid

This file constructs the uniform matroid `U_{r,E}` on a finite ground set `E` and proves that
the coefficients of its characteristic polynomial form a log-concave sequence, i.e. the
Adiprasito–Huh–Katz theorem for uniform matroids.
-/

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The uniform matroid `U_{r,E}`: the independent sets are the subsets of `E` of size at most
`r`. -/
noncomputable def unifOn (E : Finset α) (r : ℕ) : Matroid α :=
  (IndepMatroid.ofFinite (E := (E : Set α)) E.finite_toSet
    (fun I => I ⊆ (E : Set α) ∧ I.ncard ≤ r)
    ⟨by simp, by simp⟩
    (fun _ _ hJ hIJ => ⟨hIJ.trans hJ.1, le_trans (Set.ncard_le_ncard hIJ
      (E.finite_toSet.subset hJ.1)) hJ.2⟩)
    (by
      rintro I J ⟨hIE, hIr⟩ ⟨hJE, hJr⟩ hlt
      have hIfin : I.Finite := E.finite_toSet.subset hIE
      obtain ⟨e, heJ, heI⟩ : ∃ e ∈ J, e ∉ I := by
        by_contra h
        push_neg at h
        exact absurd (Set.ncard_le_ncard h hIfin) (by omega)
      refine ⟨e, heJ, heI, Set.insert_subset (hJE heJ) hIE, ?_⟩
      rw [Set.ncard_insert_of_notMem heI hIfin]
      omega)
    (fun _ h => h.1)).matroid

theorem unifOn_indep_iff (E : Finset α) (r : ℕ) (I : Set α) :
    (unifOn E r).Indep I ↔ I ⊆ (E : Set α) ∧ I.ncard ≤ r := by
  simp [unifOn]

private lemma enat_cast_min (a b : ℕ) : ((min a b : ℕ) : ℕ∞) = min (a : ℕ∞) (b : ℕ∞) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h : (a : ℕ∞) ≤ b)]
  · rw [min_eq_right h, min_eq_right (by exact_mod_cast h : (b : ℕ∞) ≤ a)]

theorem eRk_unifOn (E : Finset α) (r : ℕ) {S : Finset α} (hS : S ⊆ E) :
    (unifOn E r).eRk (S : Set α) = min (S.card : ℕ∞) (r : ℕ∞) := by
  apply le_antisymm
  · rw [Matroid.eRk_le_iff]
    intro I hIS hI
    rw [unifOn_indep_iff] at hI
    have hIfin : I.Finite := (S.finite_toSet).subset hIS
    refine le_min ?_ ?_
    · rw [← Set.encard_coe_eq_coe_finsetCard]
      exact Set.encard_le_encard hIS
    · rw [← hIfin.cast_ncard_eq]
      exact_mod_cast hI.2
  · rw [Matroid.le_eRk_iff]
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (n := min S.card r) (s := S) (by omega)
    refine ⟨(T : Set α), by exact_mod_cast hTS, ?_, ?_⟩
    · rw [unifOn_indep_iff]
      refine ⟨by exact_mod_cast hTS.trans hS, ?_⟩
      rw [Set.ncard_coe_finset, hT]
      omega
    · rw [Set.encard_coe_eq_coe_finsetCard, hT, enat_cast_min]

theorem matroidRank_unifOn (E : Finset α) (r : ℕ) {S : Finset α} (hS : S ⊆ E) :
    matroidRank (unifOn E r) (S : Set α) = min S.card r := by
  rw [matroidRank, eRk_unifOn E r hS, ← enat_cast_min]
  simp

/-- The characteristic polynomial of the uniform matroid, grouped by the size of the subset. -/
theorem charPoly_unifOn (E : Finset α) (r : ℕ) (hr : r ≤ E.card) :
    charPoly (unifOn E r) E =
      ∑ k ∈ Finset.range (E.card + 1),
        C ((-1 : ℤ) ^ k * (E.card.choose k : ℤ)) * X ^ (r - min k r) := by
  have h1 : charPoly (unifOn E r) E
      = ∑ S ∈ E.powerset, (-1 : Polynomial ℤ) ^ S.card * X ^ (r - min S.card r) := by
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mem_powerset] at hS
    rw [matroidRank_unifOn E r hS, matroidRank_unifOn E r (subset_refl E),
      min_eq_right hr]
  rw [h1, Finset.sum_powerset]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun S hS => by
      rw [(Finset.mem_powersetCard.mp hS).2]),
    Finset.sum_const, Finset.card_powersetCard]
  simp [nsmul_eq_mul]
  ring

/-- The partial alternating sums of binomial coefficients. -/
theorem alternating_partial_sum (n m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * ((n + 1).choose k : ℤ)
      = (-1 : ℤ) ^ m * (n.choose m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' n m]
    push_cast
    ring

private lemma natAbs_signed (m c : ℕ) : ((-1 : ℤ) ^ m * (c : ℤ)).natAbs = c := by
  rcases Nat.even_or_odd m with h | h
  · rw [h.neg_one_pow, one_mul, Int.natAbs_natCast]
  · rw [h.neg_one_pow, neg_one_mul, Int.natAbs_neg, Int.natAbs_natCast]

/-- The coefficients of the characteristic polynomial of `U_{r,E}`, as a sum over subset sizes. -/
theorem coeff_charPoly_unifOn (E : Finset α) (r i : ℕ) (hr : r ≤ E.card) :
    (charPoly (unifOn E r) E).coeff i
      = ∑ k ∈ Finset.range (E.card + 1),
          ((-1 : ℤ) ^ k * (E.card.choose k : ℤ)) * (if i = r - min k r then 1 else 0) := by
  rw [charPoly_unifOn E r hr, Polynomial.finset_sum_coeff]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

/-- The coefficients of the characteristic polynomial of `U_{r,E}` in positive degrees. -/
theorem whitneyAbs_unifOn_pos (E : Finset α) (r i : ℕ) (hr : r ≤ E.card) (hi : 1 ≤ i) :
    whitneyAbs (unifOn E r) E i = if i ≤ r then E.card.choose (r - i) else 0 := by
  rw [whitneyAbs, coeff_charPoly_unifOn E r i hr]
  split_ifs with hir
  · rw [Finset.sum_eq_single (r - i)]
    · rw [if_pos (by omega), mul_one, natAbs_signed]
    · intro k _ hne
      rw [if_neg (by rcases le_total r k with h | h <;> simp [h] <;> omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Finset.sum_eq_zero fun k _ => by rw [if_neg (by omega), mul_zero]]
    rfl

/-- The constant coefficient of the characteristic polynomial of `U_{r,E}`. -/
theorem whitneyAbs_unifOn_zero (E : Finset α) (r : ℕ) (hr : r ≤ E.card) (hr0 : 1 ≤ r) :
    whitneyAbs (unifOn E r) E 0 = (E.card - 1).choose (r - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, E.card = m + 1 := ⟨E.card - 1, by omega⟩
  rw [whitneyAbs, coeff_charPoly_unifOn E (j + 1) 0 hr, hm]
  rw [hm] at hr
  have hsplit : ∑ k ∈ Finset.range (m + 1 + 1),
        ((-1 : ℤ) ^ k * ((m + 1).choose k : ℤ)) * (if 0 = j + 1 - min k (j + 1) then 1 else 0)
      = ∑ k ∈ Finset.Ico (j + 1) (m + 1 + 1), ((-1 : ℤ) ^ k * ((m + 1).choose k : ℤ)) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_total (j + 1) k with h | h
      · exact ⟨h, h1⟩
      · simp [h] at h2; omega
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by simp [min_eq_right h1]⟩
  have htot : ∑ k ∈ Finset.range (m + 1 + 1), ((-1 : ℤ) ^ k * ((m + 1).choose k : ℤ)) = 0 := by
    rw [Int.alternating_sum_range_choose, if_neg (by omega)]
  rw [hsplit, Finset.sum_Ico_eq_sub _ (by omega), htot, alternating_partial_sum m j]
  simp only [Nat.add_sub_cancel, zero_sub]
  rw [Int.natAbs_neg]
  exact natAbs_signed j _

/-- **Log-concavity of the characteristic polynomial of a matroid** (Adiprasito–Huh–Katz), proved
here in the special case of uniform matroids: for the uniform matroid `U_{r,E}` of rank
`1 ≤ r ≤ |E|` on a finite ground set `E`, the absolute values `w_i` of the coefficients of the
characteristic polynomial form a log-concave sequence, `w_i · w_{i+2} ≤ w_{i+1}^2`.
The free (Boolean) matroid is the case `r = |E|` (see `Frontier.freeOn_eq_unifOn`). -/
theorem huh_matroid_log_concave (E : Finset α) (r : ℕ) (hr : r ≤ E.card) (hr0 : 1 ≤ r)
    (i : ℕ) :
    whitneyAbs (unifOn E r) E i * whitneyAbs (unifOn E r) E (i + 2)
      ≤ whitneyAbs (unifOn E r) E (i + 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [whitneyAbs_unifOn_zero E r hr hr0, whitneyAbs_unifOn_pos E r 1 hr le_rfl,
      whitneyAbs_unifOn_pos E r 2 hr (by omega)]
    rcases lt_or_ge r 2 with h2 | h2
    · rw [if_neg (by omega), mul_zero]
      exact Nat.zero_le _
    · rw [if_pos (by omega), if_pos (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
      obtain ⟨m, hm⟩ : ∃ m, E.card = m + 1 := ⟨E.card - 1, by omega⟩
      have hle : (E.card - 1).choose (k + 1) ≤ E.card.choose (k + 2) := by
        rw [hm, Nat.add_sub_cancel, Nat.choose_succ_succ' m (k + 1)]
        omega
      have s1 : k + 2 - 1 = k + 1 := by omega
      have s2 : k + 2 - 2 = k := by omega
      rw [s1, s2]
      calc (E.card - 1).choose (k + 1) * E.card.choose k
          ≤ E.card.choose (k + 2) * E.card.choose k := Nat.mul_le_mul_right _ hle
        _ = E.card.choose k * E.card.choose (k + 2) := Nat.mul_comm _ _
        _ ≤ E.card.choose (k + 1) ^ 2 := by
            rw [pow_two]; exact choose_log_concave E.card k
  · rw [whitneyAbs_unifOn_pos E r i hr hi, whitneyAbs_unifOn_pos E r (i + 1) hr (by omega),
      whitneyAbs_unifOn_pos E r (i + 2) hr (by omega)]
    rcases le_or_gt (i + 2) r with h | h
    · rw [if_pos h, if_pos (by omega), if_pos (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, r - i = k + 2 := ⟨r - i - 2, by omega⟩
      have e1 : r - (i + 1) = k + 1 := by omega
      have e2 : r - (i + 2) = k := by omega
      rw [hk, e1, e2, pow_two, Nat.mul_comm]
      exact choose_log_concave E.card k
    · rw [if_neg (show ¬ (i + 2 ≤ r) by omega), mul_zero]
      exact Nat.zero_le _

/-- The free matroid on `E` is the uniform matroid of rank `|E|` on `E`. -/
theorem freeOn_eq_unifOn (E : Finset α) : Matroid.freeOn (E : Set α) = unifOn E E.card := by
  refine Matroid.ext_indep ?_ fun I hI => ?_
  · simp [unifOn]
  · rw [Matroid.freeOn_indep_iff, unifOn_indep_iff]
    simp only [Matroid.freeOn_ground] at hI
    have hcard : I.ncard ≤ E.card := by
      simpa [Set.ncard_coe_finset] using Set.ncard_le_ncard hI E.finite_toSet
    simp [hI, hcard]

/-! ### A sanity check

For the uniform matroid `U_{2,3}` (three points on a line) the characteristic polynomial is
`t^2 - 3t + 2`, so the Whitney numbers are `w_2 = 1`, `w_1 = 3`, `w_0 = 2`. -/

example : whitneyAbs (unifOn ({0, 1, 2} : Finset ℕ) 2) ({0, 1, 2} : Finset ℕ) 2 = 1 := by
  rw [whitneyAbs_unifOn_pos _ _ _ (by decide) (by norm_num)]
  decide

example : whitneyAbs (unifOn ({0, 1, 2} : Finset ℕ) 2) ({0, 1, 2} : Finset ℕ) 1 = 3 := by
  rw [whitneyAbs_unifOn_pos _ _ _ (by decide) (by norm_num)]
  decide

example : whitneyAbs (unifOn ({0, 1, 2} : Finset ℕ) 2) ({0, 1, 2} : Finset ℕ) 0 = 2 := by
  rw [whitneyAbs_unifOn_zero _ _ (by decide) (by norm_num)]
  decide

end Frontier

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

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The rank of a set in a matroid, as a natural number. -/
noncomputable def matroidRank (M : Matroid α) (X : Set α) : ℕ := (M.eRk X).toNat

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`, defined by the
Whitney rank-generating formula
`χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)}`. -/
noncomputable def charPoly (M : Matroid α) (E : Finset α) : Polynomial ℤ :=
  ∑ S ∈ E.powerset, (-1) ^ S.card * X ^ (matroidRank M E - matroidRank M (S : Set α))

/-- The absolute values of the coefficients of the characteristic polynomial (the Whitney numbers
of the first kind, up to sign). -/
noncomputable def whitneyAbs (M : Matroid α) (E : Finset α) (i : ℕ) : ℕ :=
  ((charPoly M E).coeff i).natAbs

/-- In the free matroid on `E`, every subset of `E` has rank equal to its cardinality. -/
lemma matroidRank_freeOn {E S : Finset α} (h : S ⊆ E) :
    matroidRank (Matroid.freeOn (E : Set α)) (S : Set α) = S.card := by
  rw [matroidRank, Matroid.eRk_freeOn (by exact_mod_cast h), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the free (Boolean) matroid on `E` is `(t - 1)^{|E|}`. -/
lemma charPoly_freeOn (E : Finset α) :
    charPoly (Matroid.freeOn (E : Set α)) E = (X - 1) ^ E.card := by
  have h1 : charPoly (Matroid.freeOn (E : Set α)) E
      = ∑ S ∈ E.powerset, (-1 : Polynomial ℤ) ^ S.card * X ^ (E.card - S.card) := by
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mem_powerset] at hS
    rw [matroidRank_freeOn hS, matroidRank_freeOn (subset_refl E)]
  rw [h1, Finset.sum_powerset]
  have h2 : ∀ j ∈ Finset.range (E.card + 1),
      (∑ S ∈ Finset.powersetCard j E, (-1 : Polynomial ℤ) ^ S.card * X ^ (E.card - S.card))
        = (-1 : Polynomial ℤ) ^ j * X ^ (E.card - j) * (E.card.choose j : Polynomial ℤ) := by
    intro j _
    rw [Finset.sum_congr rfl (fun S hS => by
      rw [(Finset.mem_powersetCard.mp hS).2]), Finset.sum_const,
      Finset.card_powersetCard]
    simp [nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl h2]
  have h3 : ((-1 : Polynomial ℤ) + X) ^ E.card
      = ∑ j ∈ Finset.range (E.card + 1),
        (-1 : Polynomial ℤ) ^ j * X ^ (E.card - j) * (E.card.choose j : Polynomial ℤ) := by
    rw [add_pow]
  rw [← h3]
  ring

/-- The Whitney numbers of the free matroid are binomial coefficients. -/
lemma whitneyAbs_freeOn (E : Finset α) (i : ℕ) :
    whitneyAbs (Matroid.freeOn (E : Set α)) E i = E.card.choose i := by
  rw [whitneyAbs, charPoly_freeOn]
  have : ((X : Polynomial ℤ) - 1) ^ E.card = (X + C (-1 : ℤ)) ^ E.card := by
    simp [sub_eq_add_neg]
  rw [this, Polynomial.coeff_X_add_C_pow]
  rw [Int.natAbs_mul]
  have hpow : ((-1 : ℤ) ^ (E.card - i)).natAbs = 1 := by
    rcases Nat.even_or_odd (E.card - i) with h | h
    · rw [h.neg_one_pow]; rfl
    · rw [h.neg_one_pow]; rfl
  rw [hpow, one_mul, Int.natAbs_natCast]

/-- Binomial coefficients form a log-concave sequence. -/
lemma choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) * n.choose (k + 1) := by
  have key : (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2))
      ≤ (n.choose (k + 1) * n.choose (k + 1)) * ((k + 1) * (k + 2)) := by
    have e1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
    have e2 : n.choose (k + 2) * (k + 2) = n.choose (k + 1) * (n - (k + 1)) :=
      Nat.choose_succ_right_eq n (k + 1)
    have lhs : (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2))
        = (n.choose k * (k + 1)) * (n.choose (k + 1) * (n - (k + 1))) := by
      rw [← e2]; ring
    have rhs : (n.choose (k + 1) * n.choose (k + 1)) * ((k + 1) * (k + 2))
        = (n.choose k * (n - k)) * (n.choose (k + 1) * (k + 2)) := by
      rw [← e1]; ring
    rw [lhs, rhs]
    have hstep : (k + 1) * (n - (k + 1)) ≤ (n - k) * (k + 2) := by
      calc (k + 1) * (n - (k + 1)) ≤ (k + 1) * (n - k) :=
            Nat.mul_le_mul_left _ (Nat.sub_le_sub_left (Nat.le_succ k) n)
        _ ≤ (k + 2) * (n - k) := Nat.mul_le_mul_right _ (by omega)
        _ = (n - k) * (k + 2) := Nat.mul_comm _ _
    calc (n.choose k * (k + 1)) * (n.choose (k + 1) * (n - (k + 1)))
        = (n.choose k * n.choose (k + 1)) * ((k + 1) * (n - (k + 1))) := by ring
      _ ≤ (n.choose k * n.choose (k + 1)) * ((n - k) * (k + 2)) :=
          Nat.mul_le_mul_left _ hstep
      _ = (n.choose k * (n - k)) * (n.choose (k + 1) * (k + 2)) := by ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- **Log-concavity of the characteristic polynomial of a matroid** (Adiprasito–Huh–Katz),
base case: for the free (Boolean) matroid on a finite ground set `E`, the absolute values of the
coefficients of the characteristic polynomial form a log-concave sequence,
`w_{i+1}^2 ≥ w_i · w_{i+2}`. -/
theorem huh_matroid_log_concave_freeOn (E : Finset α) (i : ℕ) :
    whitneyAbs (Matroid.freeOn (E : Set α)) E i * whitneyAbs (Matroid.freeOn (E : Set α)) E (i + 2)
      ≤ whitneyAbs (Matroid.freeOn (E : Set α)) E (i + 1) ^ 2 := by
  simp only [whitneyAbs_freeOn, pow_two]
  exact choose_log_concave E.card i

end Frontier

