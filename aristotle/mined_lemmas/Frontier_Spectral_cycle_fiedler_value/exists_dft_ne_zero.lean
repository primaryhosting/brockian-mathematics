/-
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

open Finset Matrix SimpleGraph

namespace Frontier.Spectral

/-! ## The root of unity `ζ = exp (2 π i / n)` -/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma exists_dft_ne_zero {n : ℕ} (hn : n ≠ 0) (y : Fin n → ℂ) (hy : y ≠ 0) :
    ∃ k : Fin n, dft n y ((k : ℕ) : ℤ) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hy
  funext i
  have h := dft_inversion hn y i
  rw [Finset.sum_congr rfl fun k _ => by rw [hcon k, zero_mul]] at h
  simp only [Finset.sum_const_zero] at h
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h0 : (n : ℂ) * y i = 0 := h.symm
  rcases mul_eq_zero.mp h0 with hc | hc
  · exact absurd hc hn'
  · simpa using hc

