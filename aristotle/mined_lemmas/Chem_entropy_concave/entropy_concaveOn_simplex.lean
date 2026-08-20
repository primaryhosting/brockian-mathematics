/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Finset

/-- The Gibbs entropy of a (finite) probability vector `p`: `S(p) = -∑ i, p i * log (p i)`,
written using Mathlib's `Real.negMulLog x = -x * log x` (so that the `p i = 0` terms vanish). -/

theorem entropy_concaveOn_simplex (n : ℕ) :
    ConcaveOn ℝ {p : Fin n → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} entropy := by
  refine (entropy_concave n).subset (fun p hp => hp.1) ?_
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => by have := hx.1 i; have := hy.1 i; dsimp; positivity, ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

end Chem

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

