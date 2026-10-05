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

theorem margOut_of_factor (sys : System V S) (A : Finset V)
    (f : ({i // i ∈ A} → S) → ({i // i ∈ A} → S) → ℝ)
    (g : ({i // i ∉ A} → S) → ({i // i ∉ A} → S) → ℝ)
    (hf : ∀ a, ∑ b, f a b = 1)
    (hfac : ∀ x y, sys.tpm x y = f (resIn A x) (resIn A y) * g (resOut A x) (resOut A y))
    (x : V → S) (v : {i // i ∉ A} → S) :
    margOut sys A x v = g (resOut A x) v := by
  have key : ∀ y : V → S, (if resOut A y = v then sys.tpm x y else 0)
      = f (resIn A x) (resIn A y)
        * (fun v' => if v' = v then g (resOut A x) v' else 0) (resOut A y) := by
    intro y
    by_cases h : resOut A y = v <;> simp [h, hfac x y]
  simp only [margOut]
  rw [Finset.sum_congr rfl (fun y _ => key y),
    sum_split_mul A (f (resIn A x)) (fun v' => if v' = v then g (resOut A x) v' else 0), hf]
  simp

