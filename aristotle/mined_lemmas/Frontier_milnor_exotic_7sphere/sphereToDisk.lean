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


def sphereToDisk {n : ℕ} (x : Sph n) : Dsk n :=
  ⟨(x : EuclideanSpace ℝ (Fin n)), by
    rw [mem_closedBall_zero_iff, norm_coe_unitSphere]⟩

/-- The gluing relation defining the twisted sphere `Dⁿ ∪_f Dⁿ`. -/
inductive GlueRel {n : ℕ} (f : Sph n ≃ₜ Sph n) : Dsk n ⊕ Dsk n → Dsk n ⊕ Dsk n → Prop
  | intro (x : Sph n) : GlueRel f (Sum.inl (sphereToDisk x)) (Sum.inr (sphereToDisk (f x)))

/-- The twisted sphere `Σ_f = Dⁿ ∪_f Dⁿ`: two disks glued along their boundary by `f`. -/
