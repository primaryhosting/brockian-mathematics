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

/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Phys

open Finset

variable {ι : Type*} [Fintype ι]

/-- Boltzmann weight of state `i` for the Hamiltonian `E - f • A` at inverse
temperature `beta`, i.e. `exp (-beta * (E i - f * A i))`. -/

theorem fluctuation_dissipation_deriv [Nonempty ι] (beta : ℝ) (E A B : ι → ℝ) (f : ℝ) :
    deriv (fun f => expect beta E A f B) f
      = beta * (expect beta E A f (fun i => A i * B i)
        - expect beta E A f A * expect beta E A f B) :=
  (fluctuation_dissipation beta E A B f).deriv

end Phys

