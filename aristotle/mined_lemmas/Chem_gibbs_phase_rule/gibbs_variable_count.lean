import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
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

namespace Chem

/-- **Counting form of the Gibbs phase rule.**

With `C ≥ 1` components distributed over `P ≥ 1` phases, the intensive state of the
system is described by `2 + P * (C - 1)` variables (temperature, pressure, and `C - 1`
independent mole fractions in each phase), while equality of the chemical potential of
each component across all phases imposes `C * (P - 1)` conditions.  The difference is
`C - P + 2`. -/

theorem gibbs_variable_count (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P) :
    ((2 + P * (C - 1) : ℕ) : ℤ) - ((C * (P - 1) : ℕ) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- The solution set of an inhomogeneous linear system `f x = b` is an affine subspace:
it is the coset `x₀ + ker f` through any particular solution `x₀`. -/
