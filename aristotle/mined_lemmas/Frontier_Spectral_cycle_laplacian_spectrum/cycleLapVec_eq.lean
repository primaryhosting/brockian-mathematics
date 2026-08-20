import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

namespace Frontier.Spectral

open Complex Matrix ZMod AddChar Finset

/-- The generating vector of the cycle Laplacian: `2` at `0`, `-1` at `±1`, `0` elsewhere. -/

lemma cycleLapVec_eq (hn : 3 ≤ n) (d : ZMod n) :
    cycleLapVec n d =
      2 * (if d = 0 then 1 else 0) - (if d = 1 then (1 : ℂ) else 0)
        - (if d = -1 then (1 : ℂ) else 0) := by
  have h1 : (1 : ZMod n) ≠ 0 := one_ne_zero_zmod hn
  have h2 : (-1 : ZMod n) ≠ 0 := neg_one_ne_zero_zmod hn
  have h3 : (1 : ZMod n) ≠ -1 := one_ne_neg_one_zmod hn
  unfold cycleLapVec
  by_cases hd0 : d = 0
  · subst hd0; simp [Ne.symm h1, Ne.symm h2]
  · by_cases hd1 : d = 1
    · subst hd1; simp [h1, h3]
    · by_cases hd2 : d = -1
      · subst hd2; simp [h2, Ne.symm h3]
      · simp [hd0, hd1, hd2]

/-- Evaluating a weighted sum against the generating vector. -/
