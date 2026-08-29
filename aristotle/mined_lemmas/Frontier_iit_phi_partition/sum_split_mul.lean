import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

/-! ## A finite-sum Gibbs inequality

The nonnegativity of a Kullback–Leibler divergence between two finitely supported
probability distributions. -/

/-- One term of Gibbs' inequality: `p - q ≤ p * log (p / q)`, under the absolute
continuity assumption `q = 0 → p = 0`. -/

theorem sum_split_mul (A : Finset V) (F : ({i // i ∈ A} → S) → ℝ)
    (G : ({i // i ∉ A} → S) → ℝ) :
    ∑ y : V → S, F (resIn A y) * G (resOut A y) = (∑ u, F u) * (∑ v, G v) := by
  rw [Fintype.sum_equiv (splitEquiv A) (fun y => F (resIn A y) * G (resOut A y))
      (fun z => F z.1 * G z.2) (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]

/-! ## Nonnegativity of effective information -/

