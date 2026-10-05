/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the required
-- header appears above as a plain block comment and is repeated as a module docstring below.)

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

namespace Phys

variable {ι : Type*} [Fintype ι]

/-- Unnormalized Boltzmann weight of the microstate `i` for the canonical ensemble at inverse
temperature `β`, with unperturbed energy `E i` and the observable `A` coupled to an external
field `f` (perturbed energy `E i - f * A i`). -/

theorem deriv_ensembleAvg [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) :
    deriv (fun f => ensembleAvg beta E A f A) f
      = beta * (ensembleAvg beta E A f (fun i => A i ^ 2) - (ensembleAvg beta E A f A) ^ 2) :=
  (fluctuation_dissipation beta E A f).deriv

/-- The equilibrium variance `⟨A²⟩ - ⟨A⟩²` is nonnegative (Cauchy-Schwarz). -/
