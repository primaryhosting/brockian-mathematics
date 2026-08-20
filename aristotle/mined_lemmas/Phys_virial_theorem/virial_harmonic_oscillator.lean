/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology

namespace Phys

/-- **Auxiliary integration-by-parts fact.**  If `f` is everywhere differentiable with
integrable derivative `f'` and `f` tends to `0` at both ends of the real line, then the
integral of `f'` over `ℝ` vanishes. -/

theorem virial_harmonic_oscillator :
    2 * ∫ x : ℝ, hoDPsi x ^ 2 = ∫ x : ℝ, x * hoDV x * hoPsi x ^ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ :=
    virial_hypotheses_nonvacuous
  exact virial_theorem h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end Phys

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

