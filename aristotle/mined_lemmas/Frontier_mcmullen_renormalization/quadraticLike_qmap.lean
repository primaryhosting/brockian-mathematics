/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/

theorem quadraticLike_qmap (hR : 2 ≤ R) (hc : ‖c‖ < R) :
    QuadraticLike (qmap c) (qmap c ⁻¹' Metric.ball (0 : ℂ) R) (Metric.ball (0 : ℂ) R) := by
  have hR1 : 1 < R := by linarith
  have hRc : R + ‖c‖ < R ^ 2 := by nlinarith
  have hclos := closure_preimage_subset (c := c) (R := R) hR1 hRc
  refine
    { isOpen_source := (Metric.isOpen_ball).preimage (continuous_qmap c)
      isOpen_target := Metric.isOpen_ball
      isCompact_closure := ?_
      closure_subset := hclos
      analyticOnNhd := ?_
      mapsTo := ?_
      degree_two := ?_ }
  · refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure ?_
    exact hclos.trans Metric.ball_subset_closedBall
  · intro z _
    exact (analyticAt_id.pow 2).add analyticAt_const
  · intro z hz; exact hz
  · have hcV : c ∈ Metric.ball (0 : ℂ) R := by
      simpa [Metric.mem_ball, dist_zero_right] using hc
    refine ⟨c, hcV, ?_, ?_⟩
    · have hs : (0 : ℂ) ^ 2 = c - c := by ring
      rw [fiber_eq hcV hs]
      simp
    · intro w hw hwc
      obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w - c := IsAlgClosed.exists_pow_nat_eq (w - c) two_pos
      rw [fiber_eq hw hs]
      refine Set.ncard_pair ?_
      intro h
      have hs0 : s = 0 := by
        have h2 : (2 : ℂ) * s = 0 := by linear_combination h
        simpa using h2
      rw [hs0] at hs
      have hwc0 : w - c = 0 := by linear_combination -hs
      exact hwc (sub_eq_zero.mp hwc0)

end Disks

/-! ## The escape criterion and the filled Julia set -/

section Julia

variable {c : ℂ} {R : ℝ}

/-- Escape estimate: outside the disk of radius `R`, orbits grow linearly. -/
