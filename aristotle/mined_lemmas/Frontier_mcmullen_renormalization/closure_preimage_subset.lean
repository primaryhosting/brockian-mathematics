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

lemma closure_preimage_subset (hR : 1 < R) (hRc : R + ‖c‖ < R ^ 2) :
    closure (qmap c ⁻¹' Metric.ball (0 : ℂ) R) ⊆ Metric.ball (0 : ℂ) R := by
  have hsub : closure (qmap c ⁻¹' Metric.ball (0 : ℂ) R) ⊆ {z : ℂ | ‖qmap c z‖ ≤ R} := by
    apply closure_minimal
    · intro z hz
      simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hz
      exact le_of_lt hz
    · exact isClosed_le (continuous_norm.comp (continuous_qmap c)) continuous_const
  intro z hz
  have h1 : ‖qmap c z‖ ≤ R := hsub hz
  have h2 : ‖z‖ ^ 2 - ‖c‖ ≤ R := le_trans (norm_qmap_ge c z) h1
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have : ‖z‖ < R := by nlinarith
  simpa [Metric.mem_ball, dist_zero_right] using this

/-- The fiber of `qmap c` over a point `w` of the target disk is `{s, -s}`,
where `s` is any square root of `w - c`. -/
