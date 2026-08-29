import Mathlib
/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

variable {n : ℕ}

/-- The Euclidean pairing `⟨c, x⟩ = ∑ⱼ cⱼ xⱼ` on `Fin n → ℝ`. -/

lemma partialDeriv_ham_action (ω : Fin n → ℝ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ)
    (I x : Fin n → ℝ) (j : Fin n) :
    partialDeriv (fun z => ham ω ε f (z, x)) j I = ω j := by
  have h1 : HasDerivAt (fun t : ℝ => dotRR ω (Function.update I j t) + ε * f x) (ω j) (I j) := by
    have : (fun t : ℝ => dotRR ω (Function.update I j t) + ε * f x)
        = fun t : ℝ => (dotRR ω I + ω j * (t - I j)) + ε * f x := by
      funext t; rw [dotRR_update]
    rw [this]
    simpa using ((((hasDerivAt_id (I j)).sub_const (I j)).const_mul (ω j)).const_add
      (dotRR ω I)).add_const (ε * f x)
  exact h1.deriv

/-- Derivative along the linear flow of the torus deformation. -/
