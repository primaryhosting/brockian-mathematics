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

lemma unbounded_of_escape (hR : 1 < R) (hRc : R + ‖c‖ < R ^ 2) {z : ℂ} (hz : R < ‖z‖) :
    z ∉ boundedOrbit (qmap c) := by
  rintro ⟨M, hM⟩
  set d : ℝ := R ^ 2 - R - ‖c‖ with hd
  have hd0 : 0 < d := by simp only [hd]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - ‖z‖) / d)
  have h1 : ‖z‖ + (n : ℝ) * d ≤ ‖(qmap c)^[n] z‖ := escape_growth hR hRc hz n
  have h2 : ‖(qmap c)^[n] z‖ ≤ M := hM n
  have h3 : (M - ‖z‖) < (n : ℝ) * d := by
    rw [div_lt_iff₀ hd0] at hn; exact hn
  linarith

/-- **Escape criterion.** For `1 < R` and `R + ‖c‖ < R ^ 2`, the filled Julia
set at radius `R` is exactly the set of points with bounded forward orbit. -/
