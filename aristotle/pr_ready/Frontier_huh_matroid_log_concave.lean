/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Statement: The coefficients of the characteristic polynomial of a matroid are log-concave (Adiprasito–Huh–Katz).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Log-concavity of the characteristic polynomial of a matroid (base case)

The Adiprasito–Huh–Katz theorem states that the coefficients `w₀, w₁, …, w_r` of the
characteristic polynomial of a matroid form a log-concave sequence in absolute value,
i.e. `|w_{k+1}|² ≥ |w_k| · |w_{k+2}|`.

Here we formalise the Whitney rank-generating definition of the characteristic polynomial
of a matroid on a finite ground type, and prove the base case of the theorem: the free
(Boolean) matroid `U_{n,n}` on an `n`-element ground set, whose characteristic polynomial
is `(X - 1)^n`, so that the absolute values of its coefficients are the binomial
coefficients `C(n, k)`, which are log-concave.
-/

namespace Frontier

open Polynomial Finset Matroid

/-- The `ℕ`-valued rank function of a matroid. -/
noncomputable def natRk {α : Type*} (M : Matroid α) (X : Set α) : ℕ := (M.eRk X).toNat

/-- The characteristic polynomial of a matroid on a finite ground type, defined by the
Whitney rank-generating formula
`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{rk(E) - rk(S)}`. -/
noncomputable def charPoly {α : Type*} [Fintype α] (M : Matroid α) : Polynomial ℤ :=
  ∑ S : Finset α, (-1) ^ S.card * X ^ (natRk M Set.univ - natRk M (S : Set α))

/-- A sequence of integers is (absolutely) log-concave when
`|w k| * |w (k+2)| ≤ |w (k+1)|²` for all `k`. -/
def AbsLogConcave (w : ℕ → ℤ) : Prop :=
  ∀ k : ℕ, (w k).natAbs * (w (k + 2)).natAbs ≤ (w (k + 1)).natAbs ^ 2

/-- Binomial coefficients are log-concave. -/
theorem choose_log_concave (n k : ℕ) : n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  rcases le_or_gt n k with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < k + 2)]; simp
  · have h1 := Nat.choose_succ_right_eq n k
    have h2 := Nat.choose_succ_right_eq n (k + 1)
    have hmul : (k + 1) * (n - (k + 1)) ≤ (k + 2) * (n - k) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hpos : 0 < (k + 2) * (n - k) := Nat.mul_pos (by omega) (by omega)
    have key : ((k + 2) * (n - k)) * (n.choose k * n.choose (k + 2))
        ≤ ((k + 2) * (n - k)) * (n.choose (k + 1)) ^ 2 := by
      calc ((k + 2) * (n - k)) * (n.choose k * n.choose (k + 2))
          = (n.choose k * (n - k)) * (n.choose (k + 2) * (k + 2)) := by ring
        _ = (n.choose (k + 1) * (k + 1)) * (n.choose (k + 1) * (n - (k + 1))) := by rw [← h1, h2]
        _ = (n.choose (k + 1)) ^ 2 * ((k + 1) * (n - (k + 1))) := by ring
        _ ≤ (n.choose (k + 1)) ^ 2 * ((k + 2) * (n - k)) := Nat.mul_le_mul_left _ hmul
        _ = ((k + 2) * (n - k)) * (n.choose (k + 1)) ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_left key hpos

/-- The coefficients of `(X - 1)^n` over `ℤ`. -/
theorem coeff_X_sub_one_pow (n k : ℕ) :
    (((X : ℤ[X]) - 1) ^ n).coeff k = (-1) ^ (n - k) * (n.choose k : ℤ) := by
  have h2 : ((X : ℤ[X]) - 1) = X + (-1) := by ring
  have hterm : ∀ b : ℕ, ((X : ℤ[X]) ^ b * (-1) ^ (n - b) * (n.choose b : ℤ[X])).coeff k
      = if b = k then (-1) ^ (n - b) * (n.choose b : ℤ) else 0 := by
    intro b
    have h3 : ((X : ℤ[X]) ^ b * (-1) ^ (n - b) * (n.choose b : ℤ[X]))
        = C ((-1) ^ (n - b) * (n.choose b : ℤ)) * X ^ b := by
      simp only [map_mul, map_pow, map_neg, map_one, Polynomial.C_eq_natCast]
      ring
    rw [h3, coeff_C_mul, coeff_X_pow]
    split_ifs with h h'
    · simp
    · exact absurd h.symm h'
    · simp_all
    · simp
  rw [h2, add_pow, Polynomial.finset_sum_coeff]
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  rw [Finset.sum_ite_eq' (range (n + 1)) k (fun b => (-1 : ℤ) ^ (n - b) * (n.choose b : ℤ))]
  split_ifs with hk
  · rfl
  · have hlt : n < k := by simpa [Nat.lt_succ_iff] using hk
    rw [Nat.choose_eq_zero_of_lt hlt]; simp

/-- The rank of a subset in the free matroid is its cardinality. -/
theorem natRk_freeOn {α : Type*} (S : Finset α) :
    natRk (Matroid.freeOn (Set.univ : Set α)) (S : Set α) = S.card := by
  unfold natRk
  rw [Matroid.eRk_freeOn (Set.subset_univ _), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the free (Boolean) matroid `U_{n,n}` is `(X - 1)^n`. -/
theorem charPoly_freeOn {α : Type*} [Fintype α] :
    charPoly (Matroid.freeOn (Set.univ : Set α)) = ((X : ℤ[X]) - 1) ^ Fintype.card α := by
  have hcard : natRk (Matroid.freeOn (Set.univ : Set α)) Set.univ = Fintype.card α := by
    have := natRk_freeOn (Finset.univ : Finset α)
    rwa [Finset.coe_univ, Finset.card_univ] at this
  have hstep : charPoly (Matroid.freeOn (Set.univ : Set α))
      = ∑ S : Finset α, (-1 : ℤ[X]) ^ S.card * X ^ (Fintype.card α - S.card) := by
    unfold charPoly
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [hcard, natRk_freeOn S]
  rw [hstep]
  have h1 : ∑ S : Finset α, (-1 : ℤ[X]) ^ S.card * X ^ (Fintype.card α - S.card)
      = ∑ S ∈ (Finset.univ : Finset α).powerset,
          (-1 : ℤ[X]) ^ S.card * X ^ (Fintype.card α - S.card) := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext s; simp
  have h2 : ((X : ℤ[X]) - 1) = (-1) + X := by ring
  rw [h1, Finset.sum_powerset]
  simp only [Finset.card_univ]
  have key : ∀ j, ∑ t ∈ Finset.powersetCard j (Finset.univ : Finset α),
      (-1 : ℤ[X]) ^ t.card * X ^ (Fintype.card α - t.card)
      = (Nat.choose (Fintype.card α) j : ℤ[X]) * ((-1) ^ j * X ^ (Fintype.card α - j)) := by
    intro j
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_powersetCard.mp ht).2])]
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ]
    simp [nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => key j), h2, add_pow]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The absolute values of the coefficients of the characteristic polynomial of the free
(Boolean) matroid are the binomial coefficients. -/
theorem natAbs_coeff_charPoly_freeOn {α : Type*} [Fintype α] (k : ℕ) :
    ((charPoly (Matroid.freeOn (Set.univ : Set α))).coeff k).natAbs
      = (Fintype.card α).choose k := by
  rw [charPoly_freeOn, coeff_X_sub_one_pow]
  rcases Nat.even_or_odd (Fintype.card α - k) with h | h
  · rw [h.neg_one_pow]; simp
  · rw [h.neg_one_pow]; simp

/-- Adding a loop to a set does not change its rank. -/
theorem natRk_insert_of_isLoop {α : Type*} (M : Matroid α) {e : α} (he : M.IsLoop e) (S : Set α) :
    natRk M (insert e S) = natRk M S := by
  have hmem : e ∈ M.closure S := he.mem_closure S
  unfold natRk
  rw [← M.eRk_insert_closure_eq e S, Set.insert_eq_self.mpr hmem, M.eRk_closure_eq]

/-- A matroid with a loop has vanishing characteristic polynomial: the involution
`S ↦ S Δ {e}` on subsets of the ground set cancels the terms of the Whitney sum in pairs. -/
theorem charPoly_eq_zero_of_isLoop {α : Type*} [Fintype α] (M : Matroid α) {e : α}
    (he : M.IsLoop e) : charPoly M = 0 := by
  unfold charPoly
  refine Finset.sum_involution (fun S _ => if e ∈ S then S.erase e else insert e S)
    (fun S _ => ?_) (fun S _ _ => ?_) (fun S _ => Finset.mem_univ _) (fun S _ => ?_)
  · by_cases hS : e ∈ S
    · simp only [hS, if_true]
      have hcoe : ((S : Set α)) = insert e ((S.erase e : Finset α) : Set α) := by
        rw [← Finset.coe_insert, Finset.insert_erase hS]
      have hrk : natRk M (S : Set α) = natRk M ((S.erase e : Finset α) : Set α) := by
        rw [hcoe]; exact natRk_insert_of_isLoop M he _
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, hS⟩
      have hcard : S.card = (S.erase e).card + 1 := by
        rw [Finset.card_erase_of_mem hS]; omega
      rw [hrk, hcard, pow_succ]
      ring
    · simp only [hS, if_false]
      have hrk : natRk M ((insert e S : Finset α) : Set α) = natRk M (S : Set α) := by
        rw [Finset.coe_insert]; exact natRk_insert_of_isLoop M he _
      have hcard : (insert e S).card = S.card + 1 := Finset.card_insert_of_notMem hS
      rw [hrk, hcard, pow_succ]
      ring
  · by_cases hS : e ∈ S
    · simp only [hS, if_true]
      intro h
      exact Finset.notMem_erase e S (by rw [h]; exact hS)
    · simp only [hS, if_false]
      intro h
      exact hS (h ▸ Finset.mem_insert_self e S)
  · by_cases hS : e ∈ S
    · simp [hS, Finset.insert_erase hS]
    · simp [hS, Finset.erase_insert hS]

/-- A matroid with a loop trivially has log-concave characteristic polynomial coefficients,
since they all vanish. -/
theorem absLogConcave_coeff_charPoly_of_isLoop {α : Type*} [Fintype α] (M : Matroid α) {e : α}
    (he : M.IsLoop e) : AbsLogConcave (fun k => (charPoly M).coeff k) := by
  intro k
  simp [charPoly_eq_zero_of_isLoop M he]

/-- **Adiprasito–Huh–Katz, base case.** The coefficients of the characteristic polynomial of
the free (Boolean) matroid `U_{n,n}` on a finite ground set form a log-concave sequence in
absolute value: `|w_k| · |w_{k+2}| ≤ |w_{k+1}|²`. -/
theorem huh_matroid_log_concave {α : Type*} [Fintype α] :
    AbsLogConcave (fun k => (charPoly (Matroid.freeOn (Set.univ : Set α))).coeff k) := by
  intro k
  simp only [natAbs_coeff_charPoly_freeOn]
  exact choose_log_concave _ k

end Frontier

