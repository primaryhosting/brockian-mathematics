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

lemma kam_hypotheses_nonvacuous (ε : ℝ) :
    Diophantine (fun _ : Fin 1 => (1 : ℝ)) 1 0 ∧
    (0 : Fin 1 → ℤ) ∉ ({fun _ => 1} : Finset (Fin 1 → ℤ)) ∧
    torusDeformation (fun _ : Fin 1 => (1 : ℝ)) ε ({fun _ => 1} : Finset (Fin 1 → ℤ))
      (fun _ => 1) (fun _ => 0) 0 = -ε := by
  refine ⟨diophantine_one, ?_, ?_⟩
  · simp only [Finset.mem_singleton]
    intro h
    have := congrFun h 0
    simp at this
  · simp [torusDeformation, dotZR, dotRR]

end Frontier

