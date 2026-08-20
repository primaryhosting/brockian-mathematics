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

def ExoticSphereExists : Prop :=
  ∃ (N : Type) (tN : TopologicalSpace N)
    (cN : @ChartedSpace (EuclideanSpace ℝ (Fin 7)) _ N tN)
    (mN : @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 7)) _ _ (EuclideanSpace ℝ (Fin 7)) _ (𝓡 7)
      ⊤ N tN cN),
    @IsExotic7Sphere N tN cN mN

/-! ## Milnor's `λ`-invariant: the arithmetic core

Milnor's exotic spheres are the total spaces `M h l` of the `S³`-bundles over `S⁴` classified by
the pair of integers `(h, l)`.  When `h + l = 1` the total space is (by an explicit Morse
function) homeomorphic to `S⁷`.  Milnor's invariant of such a total space is the residue
`λ (M h l) = (h - l)² - 1  (mod 7)`,
which vanishes for the standard sphere (the case `h = 1`, `l = 0`).  The arithmetic base case of
Milnor's argument is the observation that this residue is *not* always `0`. -/

/-- Milnor's `λ`-invariant of the `S³`-bundle over `S⁴` with Euler/Pontryagin data `(h, l)`,
as a residue modulo `7`. -/
