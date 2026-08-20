import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
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

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

@[simp] lemma scaledSchwartz_apply (c : ℝ) (hc : 0 < c) (U : SchwartzMap E3 E3) (x : E3) :
    scaledSchwartz c hc U x = c • U (c • x) := by
  simp [scaledSchwartz]

/-- **Reduction to small initial energy.**  If, for some fixed `ε > 0`, every divergence free
Schwartz datum of kinetic energy less than `ε` launches a global smooth finite energy solution,
then global regularity holds for *all* divergence free Schwartz data.  Indeed, the
Navier–Stokes scaling `u₀ ↦ c u₀(c ·)` divides the energy by `c`, and it maps solutions to
solutions in both directions. -/
