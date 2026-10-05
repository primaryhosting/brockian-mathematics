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

open Matrix

/-- The graph Laplacian of the cycle graph `C n`: the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

lemma cycleEig_eq {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    cycleEig n k = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  set t : ℝ := 2 * Real.pi * k / n with ht
  have hpow : cycleRoot n ^ k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [cycleRoot, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    field_simp
  rw [cycleEig, hpow, ← Complex.exp_neg]
  have hcos : Complex.cos (t : ℂ)
      = (Complex.exp ((t:ℂ) * Complex.I) + Complex.exp (-((t:ℂ) * Complex.I))) / 2 := by
    rw [Complex.cos]; ring_nf
  push_cast [Complex.ofReal_cos]
  rw [hcos]
  ring

