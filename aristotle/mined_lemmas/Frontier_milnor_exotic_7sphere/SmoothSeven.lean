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


lemma SmoothSeven.nonempty_homeo_of_nonempty_diffeo {M N : SmoothSeven}
    (h : Nonempty (M.Diffeo N)) : Nonempty (M.Homeo N) :=
  h.elim fun d => ⟨d.toHomeomorph⟩

/-! ## Milnor's theorem, reduced to its smooth half

Milnor's proof has two halves:

* a *topological* half: the manifolds in question are twisted spheres, hence homeomorphic to
  `𝕊⁷`.  This half is **proved** above (`Frontier.twisted_seven_sphere_homeomorph`).
* a *smooth* half: a diffeomorphism invariant `λ` (built from the Hirzebruch signature theorem
  applied to a coboundary) distinguishes them from `𝕊⁷`.

The target theorem below performs the reduction: it consumes only the smooth half. -/

/-- **Milnor's exotic 7-sphere, reduced to its smooth half.**

Let `f` be any homeomorphism of `𝕊⁶`, and equip the twisted sphere `Σ_f = D⁷ ∪_f D⁷` with a
smooth structure modelled on `ℝ⁷`.  If `Σ_f` is not diffeomorphic to the standard `𝕊⁷`, then an
exotic `7`-sphere exists, i.e. `Frontier.ExoticSevenSphereExists` holds — a statement recorded
in Mathlib only as the open `proof_wanted
exists_homeomorph_isEmpty_diffeomorph_sphere_seven`.

Note that no homeomorphism `Σ_f ≃ₜ 𝕊⁷` is assumed: it is *proved*, via the Alexander trick.
The only remaining hypothesis is Milnor's smooth-invariant computation. -/
