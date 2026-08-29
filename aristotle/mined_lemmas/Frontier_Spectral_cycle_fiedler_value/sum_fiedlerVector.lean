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

namespace Frontier.Spectral

open Finset ZMod

/-- The Laplacian matrix of the cycle graph `C n` on the vertex set `ZMod n`:
diagonal entries `2` (each vertex has degree `2`), and `-1` in position `(i, j)`
whenever `j = i + 1` or `j = i - 1`. -/

lemma sum_fiedlerVector (h3 : 3 ≤ n) : ∑ i : ZMod n, fiedlerVector n i = 0 := by
  have h : (1 : ZMod n) ≠ 0 := by
    rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by simp, Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd one_pos hd; omega
  have h1 : ∑ i : ZMod n, ZMod.stdAddChar i
      = ∑ i : ZMod n, ZMod.stdAddChar ((1 : ZMod n) * i) := by simp
  have hzero : ∑ i : ZMod n, ZMod.stdAddChar i = 0 := by
    rw [h1, sum_stdAddChar_mul, if_neg h]
  unfold fiedlerVector
  rw [← Complex.re_sum, hzero, Complex.zero_re]

/-- The Fiedler vector is an eigenvector with eigenvalue `2 - 2 cos (2π/n)`. -/
