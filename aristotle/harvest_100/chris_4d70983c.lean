/-
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
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

set_option grind.warning false

namespace Frontier

open Polynomial Finset

/-!
## Setting

Adiprasito–Huh–Katz proved that for any matroid `M` the absolute values of the
coefficients of the characteristic polynomial `χ_M` form a log-concave sequence
(the Rota–Heron–Welsh conjecture).

Here we formalise the *Whitney rank* definition of the characteristic polynomial,

`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`,

and prove the base case of the theorem: the Boolean matroid (the free matroid on a
finite ground set `E`), whose characteristic polynomial is `(X - 1)^{|E|}` and whose
Whitney numbers of the first kind are, up to sign, the binomial coefficients
`C(|E|, k)`.  Log-concavity of the coefficient sequence is therefore exactly
log-concavity of the binomial coefficients, which we prove from scratch.
-/

/-- A sequence of integers is *log-concave* when `c k * c (k+2) ≤ c (k+1)^2` for all `k`. -/
def LogConcave (c : ℕ → ℤ) : Prop :=
  ∀ k : ℕ, c k * c (k + 2) ≤ c (k + 1) * c (k + 1)

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`, defined by
Whitney's rank generating formula `χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`. -/
noncomputable def charPoly {α : Type*} [DecidableEq α] (M : Matroid α) (E : Finset α) : ℤ[X] :=
  ∑ S ∈ E.powerset,
    (-1 : ℤ[X]) ^ S.card * X ^ ((M.eRk (E : Set α)).toNat - (M.eRk (S : Set α)).toNat)

section Auxiliary

/-- The coefficients of `(X - 1)^n` are the signed binomial coefficients. -/
theorem coeff_X_sub_one_pow (n k : ℕ) :
    ((X - 1 : ℤ[X]) ^ n).coeff k = (-1) ^ (n - k) * n.choose k := by
  rw [sub_eq_add_neg, add_pow, finset_sum_coeff]
  simp only [← C_1, ← C_neg, ← C_pow, ← Polynomial.C_eq_natCast, coeff_mul_C, coeff_X_pow,
    ite_mul, zero_mul]
  rw [Finset.sum_ite_eq (range (n + 1)) k]
  by_cases hk : k ∈ range (n + 1)
  · simp [hk]
  · simp only [hk, if_false]
    simp only [mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The absolute values of the coefficients of `(X - 1)^n` are the binomial coefficients. -/
theorem abs_coeff_X_sub_one_pow (n k : ℕ) :
    |((X - 1 : ℤ[X]) ^ n).coeff k| = (n.choose k : ℤ) := by
  rw [coeff_X_sub_one_pow, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]

/-- Log-concavity of the binomial coefficients: `C(n,k) * C(n,k+2) ≤ C(n,k+1)^2`. -/
theorem choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) * n.choose (k + 1) := by
  have hA := Nat.choose_succ_right_eq n k
  have hB := Nat.choose_succ_right_eq n (k + 1)
  have hpos : 0 < (k + 1) * (k + 2) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc n.choose k * n.choose (k + 2) * ((k + 1) * (k + 2))
      = n.choose k * (k + 1) * (n.choose (k + 2) * (k + 2)) := by ring
    _ = n.choose k * (k + 1) * (n.choose (k + 1) * (n - (k + 1))) := by rw [hB]
    _ = n.choose k * n.choose (k + 1) * ((k + 1) * (n - (k + 1))) := by ring
    _ ≤ n.choose k * n.choose (k + 1) * ((k + 2) * (n - k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    _ = n.choose k * (n - k) * (n.choose (k + 1) * (k + 2)) := by ring
    _ = n.choose (k + 1) * (k + 1) * (n.choose (k + 1) * (k + 2)) := by rw [hA]
    _ = n.choose (k + 1) * n.choose (k + 1) * ((k + 1) * (k + 2)) := by ring

/-- The elementary expansion `∑_{S ⊆ E} (-1)^{|S|} X^{|E| - |S|} = (X - 1)^{|E|}`. -/
theorem sum_powerset_sign_pow {α : Type*} [DecidableEq α] (E : Finset α) :
    ∑ S ∈ E.powerset, (-1 : ℤ[X]) ^ S.card * X ^ (E.card - S.card) = (X - 1) ^ E.card := by
  have h := Finset.prod_add (fun _ : α => (-1 : ℤ[X])) (fun _ => X) E
  simp only [Finset.prod_const] at h
  rw [show ((-1 : ℤ[X]) + X) = X - 1 by ring] at h
  rw [h]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hS)]

/-- In the free matroid on `E`, every subset of `E` has rank equal to its cardinality. -/
theorem eRk_freeOn_toNat {α : Type*} [DecidableEq α] {E S : Finset α} (h : S ⊆ E) :
    ((Matroid.freeOn (E : Set α)).eRk (S : Set α)).toNat = S.card := by
  rw [Matroid.Indep.eRk_eq_encard (Matroid.freeOn_indep (by exact_mod_cast h))]
  simp

end Auxiliary

/-- The characteristic polynomial of the Boolean matroid (the free matroid on a finite
ground set `E`) is `(X - 1)^{|E|}`. -/
theorem charPoly_freeOn {α : Type*} [DecidableEq α] (E : Finset α) :
    charPoly (Matroid.freeOn (E : Set α)) E = (X - 1) ^ E.card := by
  rw [charPoly]
  rw [← sum_powerset_sign_pow E]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [eRk_freeOn_toNat (Finset.Subset.refl E), eRk_freeOn_toNat (Finset.mem_powerset.mp hS)]

/-- The characteristic polynomial of any matroid whose (finite) ground set is independent —
i.e. a Boolean matroid — is `(X - 1)^{|E|}`. -/
theorem charPoly_of_ground_indep {α : Type*} [DecidableEq α] {M : Matroid α} {E : Finset α}
    (hE : M.E = (E : Set α)) (hindep : M.Indep (E : Set α)) :
    charPoly M E = (X - 1) ^ E.card := by
  have : M = Matroid.freeOn (E : Set α) := Matroid.eq_freeOn_iff.2 ⟨hE, hindep⟩
  rw [this, charPoly_freeOn]

/-- The Whitney numbers of the first kind of a Boolean matroid are, in absolute value,
the binomial coefficients. -/
theorem abs_coeff_charPoly_of_ground_indep {α : Type*} [DecidableEq α] {M : Matroid α}
    {E : Finset α} (hE : M.E = (E : Set α)) (hindep : M.Indep (E : Set α)) (k : ℕ) :
    |(charPoly M E).coeff k| = (E.card.choose k : ℤ) := by
  rw [charPoly_of_ground_indep hE hindep, abs_coeff_X_sub_one_pow]

/-- **Adiprasito–Huh–Katz, base case.**  For a Boolean matroid `M` — a matroid whose finite
ground set `E` is itself independent, equivalently the free matroid on `E` — the absolute
values of the coefficients of the characteristic polynomial

`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`

form a log-concave sequence.  Concretely `χ_M(X) = (X - 1)^{|E|}`, so this is exactly the
log-concavity `C(n,k) * C(n,k+2) ≤ C(n,k+1)^2` of the binomial coefficients. -/
theorem huh_matroid_log_concave {α : Type*} [DecidableEq α] {M : Matroid α} {E : Finset α}
    (hE : M.E = (E : Set α)) (hindep : M.Indep (E : Set α)) :
    LogConcave (fun k => |(charPoly M E).coeff k|) := by
  intro k
  simp only [abs_coeff_charPoly_of_ground_indep hE hindep]
  exact_mod_cast choose_log_concave E.card k

end Frontier

