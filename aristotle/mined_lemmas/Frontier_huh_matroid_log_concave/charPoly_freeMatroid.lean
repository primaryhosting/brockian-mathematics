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
