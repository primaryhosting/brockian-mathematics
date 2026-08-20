import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

open Complex Matrix Polynomial

/-- The cyclic shift matrix indexed by `ZMod n`: the circulant matrix whose `(i, j)` entry is `1`
exactly when `i - j = 1`. -/

lemma zmod_zero_one_neg_one_distinct (n : ℕ) (hn : 3 ≤ n) :
    (1 : ZMod n) ≠ 0 ∧ (1 : ZMod n) ≠ -1 ∧ (-1 : ZMod n) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  haveI : Fact (1 < m + 1) := ⟨by omega⟩
  have h1 : (1 : ZMod (m + 1)).val = 1 := ZMod.val_one _
  have h2 : (-1 : ZMod (m + 1)).val = m := ZMod.val_neg_one m
  have h0 : (0 : ZMod (m + 1)).val = 0 := ZMod.val_zero
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    [(rw [h, h0] at h1); (rw [h, h2] at h1); (rw [h, h0] at h2)] <;> omega

/-- The Laplacian is the polynomial `2 - X - X ^ (n - 1)` evaluated at the shift matrix. -/
