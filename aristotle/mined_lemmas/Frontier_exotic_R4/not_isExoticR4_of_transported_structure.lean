/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Manifold ContDiff Topology

namespace Frontier

/-- The standard model space `ℝ⁴` (as a Euclidean space). -/
abbrev EuclideanR4 : Type := EuclideanSpace ℝ (Fin 4)

/-- A smooth (`C^∞`) `4`-manifold: a topological space with an atlas of charts modelled on
`ℝ⁴` whose transition maps are smooth. -/
structure SmoothManifold4 where
  /-- The underlying set of points. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charts : ChartedSpace EuclideanR4 carrier]
  [smooth : IsManifold (𝓡 4) ∞ carrier]

attribute [instance] SmoothManifold4.topology SmoothManifold4.charts SmoothManifold4.smooth

/-- `M` is an *exotic* `ℝ⁴`: it is homeomorphic to `ℝ⁴`, but there is no diffeomorphism
between `M` and `ℝ⁴` with its standard smooth structure. -/

theorem not_isExoticR4_of_transported_structure
    (X : Type) [TopologicalSpace X] (h : X ≃ₜ EuclideanR4) :
    letI : Nonempty X := ⟨h.symm 0⟩
    letI : ChartedSpace EuclideanR4 X := h.isOpenEmbedding.singletonChartedSpace
    haveI : IsManifold (𝓡 4) ∞ X := h.isOpenEmbedding.isManifold_singleton (I := 𝓡 4) (n := ∞)
    ¬ IsExoticR4 ⟨X⟩ := by
  letI : Nonempty X := ⟨h.symm 0⟩
  letI : ChartedSpace EuclideanR4 X := h.isOpenEmbedding.singletonChartedSpace
  haveI : IsManifold (𝓡 4) ∞ X := h.isOpenEmbedding.isManifold_singleton (I := 𝓡 4) (n := ∞)
  rintro ⟨-, hd⟩
  refine hd.elim
    { toEquiv := h.toEquiv
      contMDiff_toFun := contMDiff_isOpenEmbedding h.isOpenEmbedding
      contMDiff_invFun := ?_ }
  have hsymm := contMDiffOn_isOpenEmbedding_symm (I := 𝓡 4) (n := ∞) h.isOpenEmbedding
  have hrange : Set.range (h : X → EuclideanR4) = Set.univ := h.surjective.range_eq
  rw [hrange] at hsymm
  refine (contMDiffOn_univ.mp hsymm).congr fun y => ?_
  conv_rhs => rw [← h.apply_symm_apply y]
  exact h.isOpenEmbedding.toOpenPartialHomeomorph_left_inv.symm

/-- The **Donaldson–Freedman input**: there is an open subset of standard `ℝ⁴` which is
homeomorphic to `ℝ⁴` but not diffeomorphic to it. This is the (deep) analytic/topological
content: Freedman's classification of simply connected topological `4`-manifolds together with
Donaldson's diagonalizability theorem produce such an open subset. -/
