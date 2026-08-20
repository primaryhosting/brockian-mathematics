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

theorem cycle_laplacian_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Set ℕ) := by
  have hn0 : n ≠ 0 := by omega
  have hspec : spectrum ℂ (cycleShift n) = {z : ℂ | z ^ n = 1} :=
    spectrum_cycleShift n (by omega)
  have hne : (spectrum ℂ (cycleShift n)).Nonempty := by
    refine ⟨1, ?_⟩
    rw [hspec]
    simp
  rw [cycleLaplacian_eq_aeval n hn, spectrum.map_polynomial_aeval_of_nonempty _ _ hne, hspec,
    rootsOfUnity_eq_image n hn0, Set.image_image]
  refine Set.image_congr ?_
  intro k _
  exact eval_at_root n k (by omega)

end Frontier.Spectral

