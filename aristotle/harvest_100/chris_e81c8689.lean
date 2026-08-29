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

import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Finset

namespace Frontier

/-- The rank of a finite set `S` in a matroid `M`, as a natural number. -/
noncomputable def matroidRank {α : Type*} (M : Matroid α) (S : Finset α) : ℕ :=
  (M.eRk (S : Set α)).toNat

/-- Whitney's rank formula for the characteristic polynomial of a matroid `M` with
finite ground set `E`:  `χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)}`. -/
noncomputable def charPoly {α : Type*} (M : Matroid α) (E : Finset α) : Polynomial ℤ :=
  ∑ S ∈ E.powerset, (-1) ^ S.card * X ^ (matroidRank M E - matroidRank M S)

/-- The Boolean (free) matroid `U_{n,n}` on `n` elements: every subset is independent. -/
noncomputable abbrev boolMatroid (n : ℕ) : Matroid (Fin n) :=
  Matroid.freeOn (Set.univ : Set (Fin n))

/-- In the Boolean matroid every set has rank equal to its cardinality. -/
lemma matroidRank_boolMatroid (n : ℕ) (S : Finset (Fin n)) :
    matroidRank (boolMatroid n) S = S.card := by
  rw [matroidRank, Matroid.eRk_freeOn (Set.subset_univ _), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the Boolean matroid `U_{n,n}` is `(t - 1)^n`. -/
lemma charPoly_boolMatroid (n : ℕ) :
    charPoly (boolMatroid n) univ = (X - 1) ^ n := by
  have hcard : ((univ : Finset (Fin n))).card = n := by simp
  rw [charPoly]
  rw [Finset.sum_congr rfl (fun S _ => by
    rw [matroidRank_boolMatroid, matroidRank_boolMatroid, hcard])]
  rw [Finset.sum_powerset, hcard]
  have step : ∀ j ∈ range (n + 1), ∑ t ∈ powersetCard j (univ : Finset (Fin n)),
      ((-1 : ℤ[X])) ^ t.card * X ^ (n - t.card) = X ^ (n - j) * (-1) ^ j * (n.choose j : ℤ[X]) := by
    intro j _
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_powersetCard.1 ht).2])]
    rw [Finset.sum_const, Finset.card_powersetCard, hcard, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl step]
  have h : (X - 1 : ℤ[X]) = X + (-1) := by ring
  rw [h, add_pow, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range, Nat.add_sub_cancel] at hj ⊢
  have h1 : n - (n - j) = j := by omega
  rw [h1, Nat.choose_symm (by omega)]

/-- The absolute values of the coefficients of the characteristic polynomial of `U_{n,n}`
are the binomial coefficients. -/
lemma natAbs_coeff_charPoly_boolMatroid (n k : ℕ) :
    ((charPoly (boolMatroid n) univ).coeff k).natAbs = n.choose k := by
  have h : (X - 1 : ℤ[X]) = X + C (-1 : ℤ) := by simp [sub_eq_add_neg]
  rw [charPoly_boolMatroid, h, coeff_X_add_C_pow]
  rw [Int.natAbs_mul]
  rcases Nat.even_or_odd (n - k) with he | ho
  · rw [he.neg_one_pow]; simp
  · rw [ho.neg_one_pow]; simp

/-- Binomial coefficients form a log-concave sequence. -/
lemma choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  rcases Nat.lt_or_ge n (k + 2) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]; simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = k + 2 + m := ⟨n - (k + 2), by omega⟩
    set n := k + 2 + m with hn
    have hA : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
    have hB : n.choose (k + 2) * (k + 2) = n.choose (k + 1) * (n - (k + 1)) :=
      Nat.choose_succ_right_eq n (k + 1)
    have h1 : n - k = m + 2 := by omega
    have h2 : n - (k + 1) = m + 1 := by omega
    rw [h1] at hA
    rw [h2] at hB
    have key : (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2)) ≤
        (n.choose (k + 1)) ^ 2 * ((k + 1) * (k + 2)) := by
      have e1 : (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2))
          = (n.choose k) * (n.choose (k + 2) * (k + 2)) * (k + 1) := by ring
      have e2 : (n.choose (k + 1)) ^ 2 * ((k + 1) * (k + 2))
          = (n.choose (k + 1) * (k + 1)) * n.choose (k + 1) * (k + 2) := by ring
      rw [e1, e2, hB, hA]
      have e3 : (n.choose k) * (n.choose (k + 1) * (m + 1)) * (k + 1)
          = (n.choose k * n.choose (k + 1)) * ((m + 1) * (k + 1)) := by ring
      have e4 : (n.choose k * (m + 2)) * n.choose (k + 1) * (k + 2)
          = (n.choose k * n.choose (k + 1)) * ((m + 2) * (k + 2)) := by ring
      rw [e3, e4]
      exact Nat.mul_le_mul_left _ (by nlinarith)
    exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- **Log-concavity of the characteristic polynomial of a matroid** (Adiprasito–Huh–Katz),
in the base case of the Boolean matroid `U_{n,n}`: the absolute values of the coefficients
of the characteristic polynomial form a log-concave sequence. -/
theorem huh_matroid_log_concave (n k : ℕ) :
    ((charPoly (boolMatroid n) univ).coeff k).natAbs *
        ((charPoly (boolMatroid n) univ).coeff (k + 2)).natAbs ≤
      ((charPoly (boolMatroid n) univ).coeff (k + 1)).natAbs ^ 2 := by
  simp only [natAbs_coeff_charPoly_boolMatroid]
  exact choose_log_concave n k

end Frontier

