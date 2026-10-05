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

/-!
## Overview

Adiprasito–Huh–Katz proved that for every matroid `M` the absolute values of the
coefficients of the characteristic polynomial

`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`  (Whitney rank formula)

form a log-concave sequence.  Here we formalise the definition of the
characteristic polynomial for a matroid with a finite ground set, and prove the
statement in the base case of the *free (Boolean) matroid* `Matroid.freeOn E`,
where the characteristic polynomial is `(X - 1)^{|E|}` and log-concavity reduces
to log-concavity of the binomial coefficients.

The main ingredients used from Mathlib are `Finset.prod_add` (binomial expansion
over a `Finset`), `Polynomial.coeff_X_add_C_pow` and `Nat.choose_succ_right_eq`.
-/

namespace Frontier

open Finset Polynomial

variable {α : Type*} [DecidableEq α]

/-- The natural-number rank of a finite set in a matroid. -/
noncomputable def natRk (M : Matroid α) (S : Finset α) : ℕ := (M.eRk (S : Set α)).toNat

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`,
defined by Whitney's rank formula
`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`. -/
noncomputable def charPoly (M : Matroid α) (E : Finset α) : Polynomial ℤ :=
  ∑ S ∈ E.powerset, (-1 : Polynomial ℤ) ^ S.card * X ^ (natRk M E - natRk M S)

omit [DecidableEq α] in
/-- In the free matroid on `E`, every subset of `E` has rank equal to its cardinality. -/
lemma natRk_freeOn {E S : Finset α} (h : S ⊆ E) :
    natRk (Matroid.freeOn (E : Set α)) S = S.card := by
  rw [natRk, Matroid.eRk_freeOn (by exact_mod_cast h), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the free (Boolean) matroid on `E` is `(X - 1)^{|E|}`. -/
lemma charPoly_freeOn (E : Finset α) :
    charPoly (Matroid.freeOn (E : Set α)) E = (X - 1) ^ E.card := by
  have h := Finset.prod_add (fun _ : α => (-1 : Polynomial ℤ)) (fun _ => X) E
  simp only [Finset.prod_const] at h
  rw [charPoly, show ((X : Polynomial ℤ) - 1) = -1 + X by ring, h]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powerset] at hS
  rw [natRk_freeOn hS, natRk_freeOn (le_refl E), Finset.card_sdiff,
    Finset.inter_eq_left.mpr hS]

/-- Coefficients of `(X - 1)^n` in `ℤ[X]`. -/
lemma coeff_X_sub_one_pow (n k : ℕ) :
    (((X : Polynomial ℤ) - 1) ^ n).coeff k = (-1) ^ (n - k) * (n.choose k : ℤ) := by
  rw [show ((X : Polynomial ℤ) - 1) = X + C (-1) by simp [sub_eq_add_neg],
    Polynomial.coeff_X_add_C_pow]

/-- Log-concavity of the binomial coefficients. -/
lemma choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) ^ 2 := by
  have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have h2 : n.choose (k + 2) * (k + 2) = n.choose (k + 1) * (n - (k + 1)) :=
    Nat.choose_succ_right_eq n (k + 1)
  have hle : (k + 1) * (n - (k + 1)) ≤ (n - k) * (k + 2) := by
    have h : n - (k + 1) ≤ n - k := by omega
    calc (k + 1) * (n - (k + 1)) ≤ (k + 2) * (n - k) := Nat.mul_le_mul (by omega) h
      _ = (n - k) * (k + 2) := Nat.mul_comm _ _
  have key : n.choose k * n.choose (k + 2) * ((k + 1) * (k + 2))
      ≤ n.choose (k + 1) ^ 2 * ((k + 1) * (k + 2)) := by
    calc n.choose k * n.choose (k + 2) * ((k + 1) * (k + 2))
        = n.choose k * (k + 1) * (n.choose (k + 2) * (k + 2)) := by ring
      _ = n.choose k * (k + 1) * (n.choose (k + 1) * (n - (k + 1))) := by rw [h2]
      _ = n.choose k * n.choose (k + 1) * ((k + 1) * (n - (k + 1))) := by ring
      _ ≤ n.choose k * n.choose (k + 1) * ((n - k) * (k + 2)) := Nat.mul_le_mul_left _ hle
      _ = n.choose k * (n - k) * (n.choose (k + 1) * (k + 2)) := by ring
      _ = n.choose (k + 1) * (k + 1) * (n.choose (k + 1) * (k + 2)) := by rw [h1]
      _ = n.choose (k + 1) ^ 2 * ((k + 1) * (k + 2)) := by ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- **Log-concavity of the characteristic polynomial of a matroid**
(Adiprasito–Huh–Katz), in the base case of the free (Boolean) matroid on a finite
ground set `E`.

The absolute values of the coefficients of the characteristic polynomial
`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}` of `M = Matroid.freeOn E`
form a log-concave sequence:  `|c_k| * |c_{k+2}| ≤ |c_{k+1}|^2`. -/
theorem huh_matroid_log_concave (E : Finset α) (k : ℕ) :
    ((charPoly (Matroid.freeOn (E : Set α)) E).coeff k).natAbs *
        ((charPoly (Matroid.freeOn (E : Set α)) E).coeff (k + 2)).natAbs
      ≤ ((charPoly (Matroid.freeOn (E : Set α)) E).coeff (k + 1)).natAbs ^ 2 := by
  have habs : ∀ j : ℕ,
      ((charPoly (Matroid.freeOn (E : Set α)) E).coeff j).natAbs = E.card.choose j := by
    intro j
    rw [charPoly_freeOn, coeff_X_sub_one_pow, Int.natAbs_mul]
    simp [Int.natAbs_pow]
  rw [habs, habs, habs]
  exact choose_log_concave _ _

end Frontier

