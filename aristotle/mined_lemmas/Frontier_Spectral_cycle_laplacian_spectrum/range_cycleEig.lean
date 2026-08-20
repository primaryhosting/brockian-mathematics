/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Finset

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

lemma range_cycleEig :
    Set.range (cycleEig n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Set ℕ) := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.val_lt, by simp [cycleEig]⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨(m : ZMod n), ?_⟩
    rw [cycleEig, ZMod.val_natCast_of_lt hm]
    push_cast
    ring

