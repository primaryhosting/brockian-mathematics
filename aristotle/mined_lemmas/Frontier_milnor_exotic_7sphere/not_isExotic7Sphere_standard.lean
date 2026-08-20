import Mathlib

/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Manifold

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

noncomputable section

/-! ## The standard smooth `7`-sphere -/

/-- `Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1`, needed to get Mathlib's smooth
manifold structure on the `7`-sphere. -/
instance factFinrankEuclidean8 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1) :=
  ⟨by simp⟩

/-- The standard round `7`-sphere `S⁷ ⊆ ℝ⁸`, with its standard smooth structure coming from
Mathlib (stereographic charts modelled on `EuclideanSpace ℝ (Fin 7)`). -/
abbrev StandardSphere7 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

example : ChartedSpace (EuclideanSpace ℝ (Fin 7)) StandardSphere7 := inferInstance
example : IsManifold (𝓡 7) ⊤ StandardSphere7 := inferInstance

/-! ## What it means to be an exotic `7`-sphere -/

/-- A smooth `7`-manifold `N` (modelled on `EuclideanSpace ℝ (Fin 7)`) is an *exotic 7-sphere*
if it is homeomorphic to the standard `7`-sphere but admits **no** diffeomorphism onto it. -/

theorem not_isExotic7Sphere_standard : ¬ IsExotic7Sphere StandardSphere7 := by
  rintro ⟨-, hempty⟩
  exact hempty.elim (Diffeomorph.refl (𝓡 7) StandardSphere7 ⊤)

/-- There exists an admissible pair with nonvanishing `λ`-invariant. -/
