import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

For a field `F` we define
`k_n(F) = K^M_n(F)/2`, the `n`-th mod-2 Milnor K-group, as the quotient of the `n`-fold
tensor power over `𝔽₂` of the square class group `F^×/(F^×)²` by the Steinberg relations
`{a, 1-a} = 0`.
-/

open scoped TensorProduct

namespace MilnorK

variable (F : Type) [Field F]

/-- The subgroup of squares of `Fˣ`. -/

theorem milnorConjecture_degree_le_one (n : ℕ) (hn : n ≤ 1) :
    Nonempty (MilnorK2 F n ≃ₗ[ZMod 2] ContCoh.H (GalF F) n) := by
  interval_cases n
  · exact ⟨LinearEquiv.ofBijective (normResidue₀ F) (voevodsky_milnor F).1⟩
  · exact ⟨LinearEquiv.ofBijective (normResidue₁ F) (voevodsky_milnor F).2⟩

end Frontier

import Mathlib

/-!
# Continuous cochain cohomology with `ZMod 2` coefficients

For a topological group `G` we define the cohomology of the complex of *continuous*
inhomogeneous cochains with values in the discrete trivial `G`-module `ZMod 2`.
This is the usual definition of Galois cohomology `Hⁿ(G, ℤ/2)` when `G` is a profinite
(e.g. absolute Galois) group.

The differential is the one from `Mathlib`'s `groupCohomology.inhomogeneousCochains`
applied to the trivial representation, so `d ∘ d = 0` comes for free.
-/

open groupCohomology inhomogeneousCochains

namespace ContCoh

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inhomogeneous `n`-cochains of `G` with values in `ZMod 2` (no continuity imposed). -/
abbrev Cochain (n : ℕ) : Type := (Fin n → G) → ZMod 2

/-- The differential on inhomogeneous cochains with trivial `ZMod 2` coefficients. -/
