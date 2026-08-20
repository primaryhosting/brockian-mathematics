/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory Metric Set Filter Function
open scoped ENNReal Topology

/-! ## The Yang–Mills energy

A Yang–Mills field on a manifold `X` is modelled here by its curvature `F : X → V`, a field with
values in a normed space `V` (in the geometric situation, `V` is the space of `𝔤`-valued
two-forms).  Its Yang–Mills energy over a region `s` is `∫_s ‖F‖²`. -/

section Energy

variable {X : Type*} [MeasurableSpace X] {V : Type*} [NormedAddCommGroup V]

/-- The Yang–Mills energy `∫_s ‖F‖²` of a curvature field `F` over the region `s`. -/

lemma exists_pos_separation (S : Finset X) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ dist x y := by
  classical
  have hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      dist x y ∈ S.offDiag.image (fun p : X × X => dist p.1 p.2) := by
    intro x hx y hy hxy
    have hmem : ((x, y) : X × X) ∈ S.offDiag := Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩
    exact Finset.mem_image_of_mem (fun p : X × X => dist p.1 p.2) hmem
  by_cases hT : (S.offDiag.image (fun p : X × X => dist p.1 p.2)).Nonempty
  · refine ⟨(S.offDiag.image (fun p : X × X => dist p.1 p.2)).min' hT, ?_, fun x hx y hy hxy => ?_⟩
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 (Finset.min'_mem _ hT)
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.1 hp
      rw [← hpe]
      exact dist_pos.2 hne
    · exact Finset.min'_le _ _ (hpair x hx y hy hxy)
  · refine ⟨1, one_pos, fun x hx y hy hxy => ?_⟩
    exact absurd (hpair x hx y hy hxy) (fun hmem => hT ⟨_, hmem⟩)

/-- **Energy quantization bound.**  Any finite family of bubbling points consumes at least
`eps` of energy each, hence has at most `Etot / eps` elements. -/
