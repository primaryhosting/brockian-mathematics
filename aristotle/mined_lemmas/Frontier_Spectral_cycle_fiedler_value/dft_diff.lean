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

lemma dft_diff (u : ZMod N → ℂ) (k : ZMod N) :
    𝓕 (fun j => u j - u (j + 1)) k = (1 - ZMod.stdAddChar k) * 𝓕 u k := by
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, sub_mul, one_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.subRight (1 : ZMod N))
    (fun j => ZMod.stdAddChar (-(j * k)) * u (j + 1))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.subRight_apply, sub_add_cancel]
  rw [show (-((j - 1) * k)) = k + (-(j * k)) by ring, AddChar.map_add_eq_mul]
  ring

end Fourier

section Gap

/-- Monotonicity input: `cos (2πm/n) ≤ cos (2π/n)` for `1 ≤ m ≤ n - 1`. -/
