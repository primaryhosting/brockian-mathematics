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


theorem milnor_exotic_7sphere_of_lambda
    (lam : SmoothSeven → ZMod 7)
    (hlam : ∀ M N : SmoothSeven, Nonempty (M.Diffeo N) → lam M = lam N)
    (Mfam : ℤ → SmoothSeven)
    (hhomeo : ∀ j : ℤ, Nonempty ((Mfam j).Homeo sphereSeven))
    (hval : ∀ j : ℤ, lam (Mfam j) = milnorLambda j)
    (hsphere : lam sphereSeven = 0) :
    ExoticSevenSphereExists := by
  obtain ⟨j, -, hj⟩ := exists_odd_milnorLambda_ne_zero
  refine milnor_exotic_7sphere_of_smooth_invariant (fun N => lam N = 0)
    (fun M N h => by simp only [hlam M N h]) (Mfam j) (hhomeo j) ?_ hsphere
  simp only [hval j]
  exact hj

end Frontier

/-! ## Axiom audit -/

#print axioms Frontier.milnor_exotic_7sphere
#print axioms Frontier.twisted_seven_sphere_homeomorph
#print axioms Frontier.milnor_exotic_7sphere_of_smooth_invariant
#print axioms Frontier.milnor_exotic_7sphere_iff
#print axioms Frontier.milnor_exotic_7sphere_of_lambda
#print axioms Frontier.no_topological_invariant_separates
#print axioms Frontier.exists_odd_milnorLambda_ne_zero
#print axioms Frontier.nonempty_twistedSphere_homeomorph_sphere
#print axioms Frontier.exists_norm_preserving_extension

import Mathlib

/-!
# The Alexander trick (cone extension of a sphere homeomorphism)

Given a homeomorphism `f` of the unit sphere of a real normed space `E`, the *cone extension*
`coneMap f` is the radial extension `x ↦ ‖x‖ • f (x / ‖x‖)` (and `0 ↦ 0`).  It is a
norm-preserving homeomorphism of `E` which restricts to `f` on the unit sphere and maps the
closed unit ball onto itself.

This is the classical *Alexander trick*, and it is the topological input which makes every
"twisted sphere" homeomorphic to the standard sphere.
-/

namespace Frontier

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
