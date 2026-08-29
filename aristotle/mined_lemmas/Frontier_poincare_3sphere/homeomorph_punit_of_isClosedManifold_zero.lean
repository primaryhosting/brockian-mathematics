/-
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

universe u

/-! ## Formalizing the statement

We formalize "closed `n`-manifold" as: a compact Hausdorff space which is locally
homeomorphic to `ℝⁿ` (i.e. carries a `ChartedSpace (EuclideanSpace ℝ (Fin n))`
structure).  "Closed" here means compact and without boundary, as usual.
-/

/-- `IsClosedManifold n M` says that the topological space `M` is a closed
(= compact, boundaryless) topological `n`-manifold: it is compact, Hausdorff and
locally homeomorphic to `EuclideanSpace ℝ (Fin n)`. -/

theorem homeomorph_punit_of_isClosedManifold_zero (M : Type u) [TopologicalSpace M]
    (h : IsClosedManifold 0 M) [ConnectedSpace M] : Nonempty (M ≃ₜ PUnit.{u + 1}) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have hopen : ∀ y : M, IsOpen ({y} : Set M) := isOpen_singleton_of_isClosedManifold_zero h
  have hclopen : IsClopen ({x} : Set M) := by
    refine ⟨?_, hopen x⟩
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    exact ⟨{y}, by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hy, hopen y, rfl⟩
  have huniv : ({x} : Set M) = Set.univ := by
    rcases isClopen_iff.mp hclopen with h0 | h1
    · exact absurd (h0 ▸ Set.mem_singleton x) (Set.notMem_empty x)
    · exact h1
  haveI : Subsingleton M := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ ({x} : Set M) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({x} : Set M) := huniv ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  haveI : Unique M := uniqueOfSubsingleton x
  exact ⟨Homeomorph.homeomorphOfUnique M PUnit⟩

end Frontier

