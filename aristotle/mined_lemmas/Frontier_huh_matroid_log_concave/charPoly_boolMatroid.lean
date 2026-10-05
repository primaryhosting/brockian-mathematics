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
