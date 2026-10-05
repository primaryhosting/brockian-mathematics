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

theorem margIn_of_factor (sys : System V S) (A : Finset V)
    (f : ({i // i ∈ A} → S) → ({i // i ∈ A} → S) → ℝ)
    (g : ({i // i ∉ A} → S) → ({i // i ∉ A} → S) → ℝ)
    (hg : ∀ a, ∑ b, g a b = 1)
    (hfac : ∀ x y, sys.tpm x y = f (resIn A x) (resIn A y) * g (resOut A x) (resOut A y))
    (x : V → S) (u : {i // i ∈ A} → S) :
    margIn sys A x u = f (resIn A x) u := by
  have key : ∀ y : V → S, (if resIn A y = u then sys.tpm x y else 0)
      = (fun u' => if u' = u then f (resIn A x) u' else 0) (resIn A y)
        * g (resOut A x) (resOut A y) := by
    intro y
    by_cases h : resIn A y = u <;> simp [h, hfac x y]
  simp only [margIn]
  rw [Finset.sum_congr rfl (fun y _ => key y),
    sum_split_mul A (fun u' => if u' = u then f (resIn A x) u' else 0) (g (resOut A x)), hg]
  simp

