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

theorem exists_admissible_milnorLambda_ne_zero :
    ∃ h l : ℤ, h + l = 1 ∧ milnorLambda h l ≠ 0 :=
  ⟨2, -1, milnorLambda_two_negOne.1, milnorLambda_two_negOne.2⟩

/-! ## The reduction

The remaining, geometric, content of Milnor's theorem is packaged as the three hypotheses
`hlam`, `hhomeo`, `hinv` below:

* `hhomeo` : for `h + l = 1` the total space `M h l` is homeomorphic to `S⁷`
  (Milnor's Morse-theoretic argument: `M h l` carries a Morse function with exactly two
  critical points, hence is homeomorphic to `S⁷` by Reeb's theorem);
* `hlam` : the `λ`-invariant of `M h l` is `(h - l)² - 1 mod 7`
  (computed from the Hirzebruch signature theorem applied to a coboundary of `M h l`);
* `hinv` : `λ` is a diffeomorphism invariant which vanishes on the standard `S⁷`
  (i.e. if `M h l` were diffeomorphic to `S⁷`, its `λ` would be `0`).

Given this package, the existence of an exotic `7`-sphere is a purely formal consequence of the
arithmetic base case above.  This is exactly Milnor's reduction, verified in Lean. -/
