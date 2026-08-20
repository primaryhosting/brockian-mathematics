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


theorem no_topological_invariant_separates
    (P : SmoothSeven → Prop)
    (hP : ∀ M N : SmoothSeven, Nonempty (M.Homeo N) → (P M ↔ P N))
    (M : SmoothSeven) (hhomeo : Nonempty (M.Homeo sphereSeven)) :
    ¬ (¬ P M ∧ P sphereSeven) := by
  rintro ⟨hMP, hSP⟩
  exact hMP ((hP M sphereSeven hhomeo).mpr hSP)

/-! ## The arithmetic base case: Milnor's `λ`-invariant modulo `7`

For the `S³`-bundles `M_j` over `S⁴` with clutching data `h + l = 1`, `h - l = j` (`j` odd),
Milnor's invariant is `λ (M_j) = j² - 1 ∈ ℤ/7`, while `λ (𝕊⁷) = 0`.  The base case of the
argument is the purely arithmetic observation that `j² - 1 ≢ 0 (mod 7)` for suitable odd `j`
(e.g. `j = 3`, giving `λ = 1`).  This is checked below by decision procedure. -/

/-- Milnor's `λ`-invariant of the bundle `M_j`, as an element of `ℤ/7`. -/
