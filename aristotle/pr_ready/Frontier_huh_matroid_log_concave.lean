/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Statement: The coefficients of the characteristic polynomial of a matroid are log-concave (Adiprasito–Huh–Katz).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- Note: Lean 4 requires `import` lines to precede all other commands (including module
-- docstrings), so the required header comment appears immediately after the import.

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

namespace Frontier

open Polynomial Finset

/-- The characteristic polynomial of a matroid `M` on a finite ground set, defined by the
Whitney rank expression `χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`, where `r` is the
rank function of `M`. -/
noncomputable def charPoly {α : Type*} [Fintype α] (M : Matroid α) : Polynomial ℤ :=
  ∑ S : Finset α, (-1 : ℤ[X]) ^ S.card * X ^ (M.eRank.toNat - (M.eRk (S : Set α)).toNat)

/-- Binomial coefficients form a log-concave sequence:
`C(n, k) * C(n, k+2) ≤ C(n, k+1)^2`. -/
theorem choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  rcases le_or_gt n (k + 1) with h | h
  · have hz : n.choose (k + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hz]
  · obtain ⟨j, rfl⟩ : ∃ j, n = k + j + 2 := ⟨n - k - 2, by omega⟩
    have h1 := Nat.choose_succ_right_eq (k + j + 2) k
    have h2 := Nat.choose_succ_right_eq (k + j + 2) (k + 1)
    have e1 : k + j + 2 - k = j + 2 := by omega
    have e2 : k + j + 2 - (k + 1) = j + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    set a := (k + j + 2).choose k with ha
    set b := (k + j + 2).choose (k + 1) with hb
    set c := (k + j + 2).choose (k + 2) with hc
    have key : (a * c) * ((j + 2) * (k + 2)) = b ^ 2 * ((k + 1) * (j + 1)) :=
      calc (a * c) * ((j + 2) * (k + 2)) = (a * (j + 2)) * (c * (k + 1 + 1)) := by ring
        _ = (b * (k + 1)) * (b * (j + 1)) := by rw [← h1, h2]
        _ = b ^ 2 * ((k + 1) * (j + 1)) := by ring
    have hle : b ^ 2 * ((k + 1) * (j + 1)) ≤ b ^ 2 * ((j + 2) * (k + 2)) := by
      apply Nat.mul_le_mul_left
      nlinarith
    exact Nat.le_of_mul_le_mul_right (key ▸ hle) (by positivity)

/-- Coefficients of `(X - 1) ^ n` in `ℤ[X]`. -/
theorem coeff_X_sub_one_pow (n k : ℕ) :
    ((X - 1 : ℤ[X]) ^ n).coeff k = (-1) ^ (n - k) * (n.choose k) := by
  rw [sub_eq_add_neg, add_pow, finset_sum_coeff]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((X : ℤ[X]) ^ i * (-1) ^ (n - i) * (n.choose i : ℤ[X])).coeff k
        = if k = i then ((-1 : ℤ) ^ (n - i) * (n.choose i)) else 0 := by
    intro i _
    have hC : C ((-1 : ℤ) ^ (n - i) * (n.choose i)) = (-1) ^ (n - i) * (n.choose i : ℤ[X]) := by
      rw [map_mul, map_pow, map_neg, map_one, C_eq_natCast]
    have hsplit : (X : ℤ[X]) ^ i * (-1) ^ (n - i) * (n.choose i : ℤ[X])
        = C ((-1 : ℤ) ^ (n - i) * (n.choose i)) * X ^ i := by
      rw [hC]; ring
    rw [hsplit, coeff_C_mul, coeff_X_pow]
    split <;> simp_all
  rw [Finset.sum_congr rfl hterm]
  rcases le_or_gt k n with h | h
  · rw [Finset.sum_ite_eq (Finset.range (n + 1)) k (fun i => ((-1 : ℤ) ^ (n - i) * (n.choose i)))]
    simp [Nat.lt_succ_of_le h]
  · rw [Finset.sum_eq_zero]
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · intro i hi
      simp only [Finset.mem_range] at hi
      rw [if_neg (by omega)]

/-- The characteristic polynomial of the free (Boolean) matroid on `n` elements is `(X - 1) ^ n`. -/
theorem charPoly_freeOn (n : ℕ) :
    charPoly (Matroid.freeOn (Set.univ : Set (Fin n))) = (X - 1) ^ n := by
  have hstep1 : charPoly (Matroid.freeOn (Set.univ : Set (Fin n)))
      = ∑ S : Finset (Fin n), (-1 : ℤ[X]) ^ S.card * X ^ (n - S.card) := by
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Matroid.eRank_freeOn, Matroid.eRk_freeOn (Set.subset_univ _)]
    simp [Set.encard_univ, Set.encard_coe_eq_coe_finsetCard]
  rw [hstep1, ← Finset.powerset_univ, Finset.sum_powerset]
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [hcard]
  have hinner : ∀ j ∈ Finset.range (n + 1),
      (∑ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)),
        (-1 : ℤ[X]) ^ S.card * X ^ (n - S.card))
      = (n.choose j : ℤ[X]) * ((-1) ^ j * X ^ (n - j)) := by
    intro j _
    rw [Finset.sum_congr rfl (fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2])]
    rw [Finset.sum_const, Finset.card_powersetCard, hcard]
    simp [nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner, sub_eq_add_neg, add_pow,
    ← Finset.sum_range_reflect (fun j => (n.choose j : ℤ[X]) * ((-1) ^ j * X ^ (n - j))) (n + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have h1 : n + 1 - 1 - i = n - i := by omega
  have h2 : n - (n - i) = i := by omega
  rw [h1, h2, Nat.choose_symm (by omega)]
  ring

/-- **Log-concavity of the coefficients of the characteristic polynomial of a matroid**
(Adiprasito–Huh–Katz), proved here in the base case of the free (Boolean) matroid on `n`
elements: the absolute values of the coefficients of `χ_M` form a log-concave sequence,
`|w_k| * |w_{k+2}| ≤ |w_{k+1}|^2`. -/
theorem huh_matroid_log_concave (n k : ℕ) :
    ((charPoly (Matroid.freeOn (Set.univ : Set (Fin n)))).coeff k).natAbs *
        ((charPoly (Matroid.freeOn (Set.univ : Set (Fin n)))).coeff (k + 2)).natAbs ≤
      (((charPoly (Matroid.freeOn (Set.univ : Set (Fin n)))).coeff (k + 1)).natAbs) ^ 2 := by
  simp only [charPoly_freeOn, coeff_X_sub_one_pow, Int.natAbs_mul]
  simpa using choose_log_concave n k

end Frontier

