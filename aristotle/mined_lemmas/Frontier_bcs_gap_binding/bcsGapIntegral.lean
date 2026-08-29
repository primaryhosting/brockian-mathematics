/-
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
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

/-- The right-hand side of the (zero-temperature, constant density of states) BCS gap
equation: the pairing integral

  `∫_0^ω dξ / √(ξ² + Δ²)`

over the energy shell `[0, ω]` around the Fermi surface, for a gap parameter `Δ`. -/

noncomputable def bcsGapIntegral (Δ ω : ℝ) : ℝ := ∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)

/-- Closed form of the BCS pairing integral for a positive gap: it equals `arsinh (ω / Δ)`. -/
