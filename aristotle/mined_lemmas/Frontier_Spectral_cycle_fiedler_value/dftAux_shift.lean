/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as a plain block comment; its text is verbatim.)

import Mathlib

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

open Finset Complex ZMod Matrix

/-! ## The Laplacian of the cycle graph -/

/-- The Laplacian matrix of the cycle graph `C n`, with vertex set `ZMod n`:
`2` on the diagonal, `-1` between neighbours `i` and `i ± 1`, `0` elsewhere. -/

lemma dftAux_shift (x : ZMod n → ℂ) (k : ZMod n) :
    dftAux n (fun j => x j - x (j + 1)) k = (1 - (stdAddChar (-k) : ℂ)) * dftAux n x k := by
  have h1 : dftAux n (fun j => x j - x (j + 1)) k
      = dftAux n x k - ∑ j : ZMod n, (stdAddChar (j * k) : ℂ) * x (j + 1) := by
    rw [dftAux, dftAux, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h2 : ∑ j : ZMod n, (stdAddChar (j * k) : ℂ) * x (j + 1)
      = (stdAddChar (-k) : ℂ) * dftAux n x k := by
    have hg := sum_shift (fun j : ZMod n => (stdAddChar ((j - 1) * k) : ℂ) * x j)
    simp only [add_sub_cancel_right] at hg
    rw [hg, dftAux, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hch : (stdAddChar ((j - 1) * k) : ℂ) = (stdAddChar (-k) : ℂ) * stdAddChar (j * k) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [hch]
    ring
  rw [h1, h2, dftAux]
  ring

end Fourier

/-! ## The spectral bound -/

