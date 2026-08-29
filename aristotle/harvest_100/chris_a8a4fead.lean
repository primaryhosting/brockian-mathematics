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

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`, in its
Whitney rank-generating form
`χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)}`. -/
noncomputable def charPoly (M : Matroid α) (E : Finset α) : Polynomial ℤ :=
  ∑ S ∈ E.powerset, (-1 : Polynomial ℤ) ^ S.card * X ^ ((M.eRk ↑E).toNat - (M.eRk ↑S).toNat)

/-- The (unsigned) Whitney numbers of the first kind: the absolute values of the
coefficients of the characteristic polynomial. -/
noncomputable def whitney (M : Matroid α) (E : Finset α) (k : ℕ) : ℕ :=
  ((charPoly M E).coeff k).natAbs

/-- Binomial coefficients are log-concave. -/
theorem choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) ^ 2 := by
  have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have h2 : n.choose (k + 2) * (k + 2) = n.choose (k + 1) * (n - (k + 1)) :=
    Nat.choose_succ_right_eq n (k + 1)
  have key : (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2)) ≤
      (n.choose (k + 1) ^ 2) * ((k + 1) * (k + 2)) := by
    have e1 : (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2))
        = (n.choose k) * (k + 1) * (n.choose (k + 2) * (k + 2)) := by ring
    have e2 : (n.choose (k + 1) ^ 2) * ((k + 1) * (k + 2))
        = (n.choose (k + 1) * (k + 1)) * (n.choose (k + 1) * (k + 2)) := by ring
    rw [e1, e2, h2, h1]
    have e3 : n.choose k * (k + 1) * (n.choose (k + 1) * (n - (k + 1)))
        = n.choose k * n.choose (k + 1) * ((k + 1) * (n - (k + 1))) := by ring
    have e4 : n.choose k * (n - k) * (n.choose (k + 1) * (k + 2))
        = n.choose k * n.choose (k + 1) * ((k + 2) * (n - k)) := by ring
    rw [e3, e4]
    have hle : (k + 1) * (n - (k + 1)) ≤ (k + 2) * (n - k) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact Nat.mul_le_mul_left _ hle
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- The rank function of the free matroid on `E` is the cardinality. -/
theorem natRank_freeOn {E S : Finset α} (h : S ⊆ E) :
    ((Matroid.freeOn (↑E : Set α)).eRk ↑S).toNat = S.card := by
  rw [Matroid.eRk_freeOn (by exact_mod_cast h), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the free (Boolean) matroid on an `n`-element set
is `(t - 1)^n`. -/
theorem charPoly_freeOn (E : Finset α) :
    charPoly (Matroid.freeOn (↑E : Set α)) E = (X - 1) ^ E.card := by
  classical
  have hE : (X - 1 : Polynomial ℤ) ^ E.card = ∏ _i ∈ E, ((-1 : Polynomial ℤ) + X) := by
    rw [Finset.prod_const]
    ring
  rw [charPoly, hE, Finset.prod_add]
  refine Finset.sum_congr rfl ?_
  intro t ht
  have hsub : t ⊆ E := Finset.mem_powerset.mp ht
  rw [Finset.prod_const, Finset.prod_const, Finset.card_sdiff_of_subset hsub,
    natRank_freeOn (Finset.Subset.refl E), natRank_freeOn hsub]

/-- The Whitney numbers of the free matroid on `E` are the binomial coefficients. -/
theorem whitney_freeOn (E : Finset α) (k : ℕ) :
    whitney (Matroid.freeOn (↑E : Set α)) E k = E.card.choose k := by
  have h : ((X : Polynomial ℤ) - 1) = X + C (-1 : ℤ) := by simp [sub_eq_add_neg]
  rw [whitney, charPoly_freeOn, h, coeff_X_add_C_pow]
  simp [Int.natAbs_mul, Int.natAbs_pow]

/-- **Adiprasito–Huh–Katz, base case.**  The coefficients of the characteristic polynomial
of a matroid form a log-concave sequence, verified here for the free (Boolean) matroid on
a finite ground set `E`: the absolute values of the coefficients of
`χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)} = (t-1)^{|E|}` satisfy
`|w_k| * |w_{k+2}| ≤ |w_{k+1}|^2`. -/
theorem huh_matroid_log_concave (E : Finset α) (M : Matroid α)
    (hM : M = Matroid.freeOn (↑E : Set α)) (k : ℕ) :
    ((charPoly M E).coeff k).natAbs * ((charPoly M E).coeff (k + 2)).natAbs ≤
      ((charPoly M E).coeff (k + 1)).natAbs ^ 2 := by
  subst hM
  have h : ∀ j : ℕ,
      ((charPoly (Matroid.freeOn (↑E : Set α)) E).coeff j).natAbs = E.card.choose j := by
    intro j
    simpa only [whitney] using whitney_freeOn E j
  rw [h k, h (k + 1), h (k + 2)]
  exact choose_log_concave E.card k

end Frontier

