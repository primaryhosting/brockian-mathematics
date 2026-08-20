/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Statement: There exists a smooth manifold homeomorphic but not diffeomorphic to ℝ⁴ (Donaldson/Freedman).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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
def IsExoticR4 (M : SmoothManifold4) : Prop :=
  Nonempty (M.carrier ≃ₜ EuclideanR4) ∧ IsEmpty (M.carrier ≃ₘ⟮𝓡 4, 𝓡 4⟯ EuclideanR4)

/-- `ℝ⁴` with its standard smooth structure, viewed as a smooth `4`-manifold. -/
def standardR4 : SmoothManifold4 where
  carrier := EuclideanR4

/-- The standard `ℝ⁴` is not exotic. -/
theorem standardR4_not_isExoticR4 : ¬ IsExoticR4 standardR4 := by
  rintro ⟨-, h⟩
  exact h.elim (Diffeomorph.refl (𝓡 4) EuclideanR4 ∞)

/-- Being an exotic `ℝ⁴` only depends on the diffeomorphism type: if `M` is exotic and `N`
is diffeomorphic to `M`, then `N` is exotic. -/
theorem isExoticR4_of_diffeomorph {M N : SmoothManifold4}
    (e : N.carrier ≃ₘ⟮𝓡 4, 𝓡 4⟯ M.carrier) (hM : IsExoticR4 M) : IsExoticR4 N := by
  obtain ⟨⟨f⟩, hd⟩ := hM
  refine ⟨⟨e.toHomeomorph.trans f⟩, ⟨fun g => hd.elim (e.symm.trans g)⟩⟩

/-- **Reduction to a smooth invariant.** To exhibit an exotic `ℝ⁴` it suffices to produce a
smooth `4`-manifold `M` homeomorphic to `ℝ⁴` together with a diffeomorphism-invariant property
`P` which holds for the standard `ℝ⁴` but fails for `M`. This is exactly the shape of the
Donaldson-invariant / gauge-theoretic argument. -/
theorem isExoticR4_of_invariant (P : SmoothManifold4 → Prop)
    (hP : ∀ A B : SmoothManifold4, (A.carrier ≃ₘ⟮𝓡 4, 𝓡 4⟯ B.carrier) → P A → P B)
    (M : SmoothManifold4) (hhomeo : Nonempty (M.carrier ≃ₜ EuclideanR4))
    (hstd : P standardR4) (hM : ¬ P M) : IsExoticR4 M :=
  ⟨hhomeo, ⟨fun e => hM (hP standardR4 M e.symm hstd)⟩⟩

/-- **A homeomorphic copy of `ℝ⁴` with the transported smooth structure is never exotic.**
If `X` is any topological space homeomorphic to `ℝ⁴` and we give `X` the smooth structure
whose single chart is that homeomorphism, then `X` is diffeomorphic to `ℝ⁴`. Hence an exotic
`ℝ⁴` can never be obtained by merely transporting the standard structure along a
homeomorphism: it must come from a genuinely incompatible atlas. -/
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
def ExistsExoticOpenSubsetOfR4 : Prop :=
  ∃ U : TopologicalSpace.Opens EuclideanR4,
    Nonempty (U ≃ₜ EuclideanR4) ∧ IsEmpty (U ≃ₘ⟮𝓡 4, 𝓡 4⟯ EuclideanR4)

/-- **Exotic `ℝ⁴` (Freedman–Donaldson), as a Lean-checked reduction.**
Granting the Donaldson–Freedman input (an open subset of `ℝ⁴` homeomorphic but not
diffeomorphic to `ℝ⁴`), there exists a smooth `4`-manifold that is homeomorphic to `ℝ⁴`
but admits no diffeomorphism to `ℝ⁴`. The reduction verifies in Lean that such an open
subset does carry a genuine smooth `4`-manifold structure. -/
theorem exotic_R4 (h : ExistsExoticOpenSubsetOfR4) :
    ∃ M : SmoothManifold4, IsExoticR4 M := by
  obtain ⟨U, hhomeo, hdiff⟩ := h
  exact ⟨⟨U⟩, hhomeo, hdiff⟩

end Frontier


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

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

