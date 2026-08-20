import Mathlib
import RequestProject.AlexanderTrick

/-!
# Twisted spheres

A *twisted sphere* is obtained by gluing two copies of the closed `n`-disk along their boundary
`𝕊ⁿ⁻¹` by a homeomorphism `f`.  All the known exotic spheres in dimension `7` arise this way
(Milnor's `S³`-bundles over `S⁴` carry Morse functions with exactly two critical points, which exhibits
them as twisted spheres).

The main result of this file is that **every twisted sphere is homeomorphic to the standard
sphere**: this is the topological half of Milnor's theorem, and it is proved here in full, for
every dimension `n`, using the Alexander trick from `RequestProject.AlexanderTrick`.
-/

namespace Frontier

open Metric

/-- The unit sphere `𝕊ⁿ⁻¹ ⊆ ℝⁿ`. -/
abbrev Sph (n : ℕ) : Type := sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The closed unit disk `Dⁿ ⊆ ℝⁿ`. -/
abbrev Dsk (n : ℕ) : Type := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1


theorem nonempty_twistedSphere_homeomorph_sphere {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    Nonempty (TwistedSphere f ≃ₜ Sph (n + 1)) :=
  ⟨twistedSphereHomeomorphSphere f⟩

end Frontier

/-
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`; the header is
-- repeated verbatim as the module docstring immediately below the imports.)
import Mathlib
import RequestProject.AlexanderTrick
import RequestProject.TwistedSphere

/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Manifold ContDiff

namespace Frontier

/-! ## Setting

`E7` is the model space `ℝ⁷`, and `S7` is the standard (round) `7`-sphere sitting inside `ℝ⁸`.
Mathlib already equips `S7` with a smooth structure modelled on `E7`.
-/

/-- The `7`-dimensional Euclidean model space `ℝ⁷`. -/
abbrev E7 : Type := EuclideanSpace ℝ (Fin 7)

/-- The standard smooth `7`-sphere `𝕊⁷ ⊆ ℝ⁸`. -/
abbrev S7 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

/-- **Statement of Milnor's theorem.**  There exists a smooth `7`-manifold which is
homeomorphic, but not diffeomorphic, to the standard `7`-sphere.

This is exactly the statement recorded (as an unproven `proof_wanted`) in Mathlib's
`Mathlib/Geometry/Manifold/PoincareConjecture.lean` under the name
`exists_homeomorph_isEmpty_diffeomorph_sphere_seven`. -/
