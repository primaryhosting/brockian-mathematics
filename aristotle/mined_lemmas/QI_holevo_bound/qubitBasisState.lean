/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/

def qubitBasisState (x : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun i => if i = x then 1 else 0)

example (x : Fin 2) : IsDensity (qubitBasisState x) := by
  constructor
  · rw [qubitBasisState, Matrix.posSemidef_diagonal_iff]
    intro i; by_cases h : i = x <;> simp [h]
  · simp [qubitBasisState, Matrix.trace, Matrix.diag]

example : SimultaneouslyDiagonalizable qubitBasisState :=
  ⟨1, Submonoid.one_mem _, fun x => ⟨fun i => if i = x then 1 else 0, by
    simp [qubitBasisState, apply_ite (fun r : ℝ => (r : ℂ))]⟩⟩

end QI

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

