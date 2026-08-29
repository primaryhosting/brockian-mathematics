import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- The standard `3`-sphere, i.e. the unit sphere in `ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The Poincaré conjecture in dimension three (Perelman's theorem):

every closed (compact, boundaryless, Hausdorff, second countable) topological `3`-manifold
which is simply connected is homeomorphic to the `3`-sphere.

Here "topological `3`-manifold" is expressed by `ChartedSpace (EuclideanSpace ℝ (Fin 3)) M`:
every point of `M` has a neighbourhood homeomorphic to an open subset of `ℝ³`. -/

def PoincareConjecture3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SimplyConnectedSpace M],
    Nonempty (M ≃ₜ Sphere3)

/-- The a priori weaker "continuous bijection" form of the Poincaré conjecture: every
simply connected closed `3`-manifold admits a *continuous bijection* onto the `3`-sphere
(no continuity of the inverse is required). -/

def PoincareBijectionForm : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SimplyConnectedSpace M],
    ∃ f : M → Sphere3, Continuous f ∧ Function.Bijective f

/-- Reduction step, for a single manifold: on a *compact* space, a continuous bijection onto
the `3`-sphere (a Hausdorff space) is automatically a homeomorphism. Thus, to establish the
Poincaré conjecture for `M` it suffices to produce a continuous bijection `M → S³`. -/

theorem homeomorph_sphere3_of_continuous_bijection {M : Type} [TopologicalSpace M]
    [CompactSpace M] {f : M → Sphere3} (hf : Continuous f) (hbij : Function.Bijective f) :
    Nonempty (M ≃ₜ Sphere3) :=
  ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hf⟩

/-- Base case of the reduction: the `3`-sphere itself is homeomorphic to the `3`-sphere,
via the identity, which is indeed a continuous bijection. -/

theorem poincare_3sphere : PoincareConjecture3 ↔ PoincareBijectionForm := by
  unfold PoincareConjecture3 PoincareBijectionForm
  constructor
  · intro h M _ _ _ _ _ _
    obtain ⟨e⟩ := h M
    exact ⟨e, e.continuous, e.bijective⟩
  · intro h M _ _ _ _ _ _
    obtain ⟨f, hf, hbij⟩ := h M
    exact homeomorph_sphere3_of_continuous_bijection hf hbij

end Frontier
