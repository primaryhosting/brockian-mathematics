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

lemma spectrum_cycleShift (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    spectrum ℂ (cycleShift n) = {z : ℂ | z ^ n = 1} := by
  refine Set.eq_of_subset_of_subset (fun z hz => ?_) (fun z hz => mem_spectrum_cycleShift n hn hz)
  have h := spectrum.map_pow_of_pos (𝕜 := ℂ) (cycleShift n) (n := n) (by omega)
  rw [cycleShift_pow_card, spectrum.one_eq] at h
  have hmem : z ^ n ∈ (fun x : ℂ => x ^ n) '' spectrum ℂ (cycleShift n) := ⟨z, hz, rfl⟩
  rw [← h] at hmem
  simpa using hmem

/-- The `n`-th roots of unity in `ℂ` are exactly the numbers `exp (2 π i k / n)`, `k < n`. -/
