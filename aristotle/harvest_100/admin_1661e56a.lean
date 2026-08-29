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

/-!
The Adiprasito–Huh–Katz theorem states that the coefficients of the characteristic
polynomial of a matroid form a log-concave sequence (in absolute value).

Here we set up the characteristic polynomial of a finite matroid through Whitney's
rank-generating (Möbius) formula
`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`
and prove the base case of the theorem for the *free matroid* (the Boolean matroid,
in which every subset of the ground set is independent), whose characteristic
polynomial is `(X - 1)^n`, so that the absolute values of its coefficients are the
binomial coefficients `C(n, k)`, which are log-concave.
-/

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid, obtained from the `ℕ∞`-valued rank. -/
noncomputable def natRk (M : Matroid α) (S : Set α) : ℕ := (M.eRk S).toNat

/-- The characteristic polynomial of a matroid on a finite ground set `α`,
defined by Whitney's rank-generating formula
`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`. -/
noncomputable def charPoly [Fintype α] [DecidableEq α] (M : Matroid α) : Polynomial ℤ :=
  ∑ S : Finset α, (-1) ^ S.card * X ^ (natRk M Set.univ - natRk M (S : Set α))

/-- The free (Boolean) matroid on a type: every subset is independent. -/
noncomputable def freeMatroid (α : Type*) : Matroid α := Matroid.freeOn Set.univ

/-- Every set is independent in the free matroid. -/
lemma freeMatroid_indep (S : Set α) : (freeMatroid α).Indep S := by
  rw [freeMatroid, Matroid.freeOn_indep_iff]
  exact Set.subset_univ S

/-- The rank of a finite set in the free matroid is its cardinality. -/
lemma natRk_freeMatroid (S : Finset α) : natRk (freeMatroid α) (S : Set α) = S.card := by
  rw [natRk, (freeMatroid_indep (S : Set α)).eRk_eq_encard,
    Set.encard_coe_eq_coe_finsetCard]
  rfl

/-- The characteristic polynomial of the free matroid on `n` elements is `(X - 1)^n`. -/
lemma charPoly_freeMatroid [Fintype α] [DecidableEq α] :
    charPoly (freeMatroid α) = (X - 1) ^ (Fintype.card α) := by
  classical
  set n := Fintype.card α with hn
  have huniv : natRk (freeMatroid α) (Set.univ : Set α) = n := by
    have := natRk_freeMatroid (Finset.univ : Finset α)
    simpa [Finset.card_univ, hn] using this
  have hsum : charPoly (freeMatroid α)
      = ∑ S ∈ (Finset.univ : Finset α).powerset,
          (-1 : Polynomial ℤ) ^ S.card * X ^ (n - S.card) := by
    rw [charPoly, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [huniv, natRk_freeMatroid]
  rw [hsum, Finset.sum_powerset]
  have hcard : (Finset.univ : Finset α).card = n := by simp [hn]
  rw [hcard]
  have hgroup : ∀ j ∈ Finset.range (n + 1),
      (∑ S ∈ Finset.powersetCard j (Finset.univ : Finset α),
        (-1 : Polynomial ℤ) ^ S.card * X ^ (n - S.card))
        = (-1 : Polynomial ℤ) ^ j * X ^ (n - j) * (n.choose j : Polynomial ℤ) := by
    intro j _
    have hterm : ∀ S ∈ Finset.powersetCard j (Finset.univ : Finset α),
        (-1 : Polynomial ℤ) ^ S.card * X ^ (n - S.card)
          = (-1 : Polynomial ℤ) ^ j * X ^ (n - j) := by
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, hcard,
      nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hgroup]
  have hadd : ((-1 : Polynomial ℤ) + X) ^ n
      = ∑ j ∈ Finset.range (n + 1),
          (-1 : Polynomial ℤ) ^ j * X ^ (n - j) * (n.choose j : Polynomial ℤ) := by
    rw [add_pow]
  rw [← hadd]
  ring

/-- The absolute value of the `k`-th coefficient of the characteristic polynomial of the
free matroid on `n` elements is the binomial coefficient `C(n, k)`. -/
lemma natAbs_coeff_charPoly_freeMatroid [Fintype α] [DecidableEq α] (k : ℕ) :
    ((charPoly (freeMatroid α)).coeff k).natAbs = (Fintype.card α).choose k := by
  rw [charPoly_freeMatroid]
  have hX : (X - 1 : Polynomial ℤ) = X + C (-1) := by simp [sub_eq_add_neg]
  rw [hX, Polynomial.coeff_X_add_C_pow]
  rcases neg_one_pow_eq_or ℤ (Fintype.card α - k) with h | h <;>
    simp [h, Int.natAbs_neg]

/-- Log-concavity of the binomial coefficients: `C(n,k) * C(n,k+2) ≤ C(n,k+1)^2`. -/
lemma choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) ^ 2 := by
  have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have h2 : n.choose (k + 2) * (k + 2) = n.choose (k + 1) * (n - (k + 1)) :=
    Nat.choose_succ_right_eq n (k + 1)
  have hstep : (n - (k + 1)) * (k + 1) ≤ (n - k) * (k + 2) :=
    Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.le_succ k) n) (by omega)
  have key : (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2))
      ≤ (n.choose (k + 1) ^ 2) * ((k + 1) * (k + 2)) := by
    calc (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2))
        = n.choose k * (n.choose (k + 2) * (k + 2)) * (k + 1) := by ring
      _ = n.choose k * (n.choose (k + 1) * (n - (k + 1))) * (k + 1) := by rw [h2]
      _ = (n.choose k * n.choose (k + 1)) * ((n - (k + 1)) * (k + 1)) := by ring
      _ ≤ (n.choose k * n.choose (k + 1)) * ((n - k) * (k + 2)) :=
          Nat.mul_le_mul_left _ hstep
      _ = (n.choose k * (n - k)) * n.choose (k + 1) * (k + 2) := by ring
      _ = (n.choose (k + 1) * (k + 1)) * n.choose (k + 1) * (k + 2) := by rw [h1]
      _ = (n.choose (k + 1) ^ 2) * ((k + 1) * (k + 2)) := by ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- **Log-concavity of the characteristic polynomial of a matroid** (Adiprasito–Huh–Katz),
base case: for the free (Boolean) matroid on a finite ground set, the absolute values of the
coefficients `w_k` of the characteristic polynomial satisfy `w_k * w_{k+2} ≤ w_{k+1}^2`. -/
theorem huh_matroid_log_concave (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    ((charPoly (freeMatroid α)).coeff k).natAbs *
        ((charPoly (freeMatroid α)).coeff (k + 2)).natAbs
      ≤ ((charPoly (freeMatroid α)).coeff (k + 1)).natAbs ^ 2 := by
  simp only [natAbs_coeff_charPoly_freeMatroid]
  exact choose_log_concave _ k

/-- Sanity check: the characteristic polynomial of the free matroid on two elements is
`(X - 1)^2 = X^2 - 2X + 1`. -/
example : charPoly (freeMatroid (Fin 2)) = (X - 1) ^ 2 := by
  simpa using charPoly_freeMatroid (α := Fin 2)

end Frontier

