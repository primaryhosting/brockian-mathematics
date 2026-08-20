/-
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as the module docstring below.)
import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Deutsch's algorithm decides whether `f : {0,1} → {0,1}` is constant or balanced using a
single query to the oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`.

The two-qubit state space is modelled as amplitude functions `Bool → Bool → ℂ`.  The
algorithm prepares `|0⟩|1⟩`, applies a Hadamard gate to each qubit, queries the oracle
exactly once, applies a Hadamard gate to the first qubit, and measures that qubit.
`QC.deutsch_correct` computes the resulting measurement distribution exactly.
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

namespace QC

/-- A two–qubit state: `ψ x y` is the amplitude of the computational basis state `|x, y⟩`. -/
abbrev State := Bool → Bool → ℂ

/-- The initial state `|0⟩ ⊗ |1⟩`. -/

theorem deutsch_decides (f : Bool → Bool) :
    (measProb f false = 1 ↔ Constant f) ∧ (measProb f false = 0 ↔ Balanced f) := by
  have h := (deutsch_correct f).1
  constructor
  · rw [h]
    constructor
    · intro hx
      by_cases hc : f false = f true
      · intro x y; cases x <;> cases y <;> first | rfl | exact hc | exact hc.symm
      · simp [hc] at hx
    · intro hc
      simp [hc false true]
  · rw [h]
    constructor
    · intro hx
      by_cases hc : f false = f true
      · simp [hc] at hx
      · exact hc
    · intro hb
      simp [Balanced] at hb
      simp [hb]

end QC

