import Mathlib

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

/-
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Filter Topology

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of a set `S ⊆ ℝ` of spectral points: the number of points
of `S` in the symmetric window `[-T, T]`.

(When `S ∩ [-T, T]` is infinite this is `0` by the junk-value convention of `Set.ncard`;
the discreteness hypothesis below rules that out.) -/

lemma exists_window_of_finset (F : Finset ℝ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ x ∈ F, x ∈ Set.Icc (-T) T := by
  obtain ⟨M, hM⟩ := Finset.exists_le (F.image (fun x => |x|))
  refine ⟨M, fun T hT x hx => ?_⟩
  have hxM : |x| ≤ M := hM _ (Finset.mem_image_of_mem _ hx)
  have hxT : |x| ≤ T := hxM.trans hT
  exact ⟨by linarith [neg_abs_le x], (le_abs_self x).trans hxT⟩

/-- **Main target.**  If the spectrum `S` is discrete (only finitely many spectral points in
each bounded symmetric window) and the Riemann–von Mangoldt input holds (there are infinitely
many spectral points), then the spectral counting function diverges to `+∞`. -/
