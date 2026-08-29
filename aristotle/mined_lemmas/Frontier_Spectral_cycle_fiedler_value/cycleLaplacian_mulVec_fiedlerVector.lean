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

lemma cycleLaplacian_mulVec_fiedlerVector (h3 : 3 ≤ n) :
    (cycleLaplacian n).mulVec (fiedlerVector n)
      = (2 - 2 * Real.cos (2 * Real.pi / n)) • fiedlerVector n := by
  have hn1 : 1 < n := by omega
  have hval : (1 : ZMod n).val = 1 := ZMod.val_one_eq_one_mod n ▸ Nat.mod_eq_of_lt hn1
  have hc : (ZMod.stdAddChar (1 : ZMod n)).re = Real.cos (2 * Real.pi / n) := by
    rw [stdAddChar_re, hval]
    norm_num
  funext i
  rw [cycleLaplacian_mulVec h3, Pi.smul_apply, smul_eq_mul]
  unfold fiedlerVector
  have e1 : ZMod.stdAddChar (i + 1) = ZMod.stdAddChar i * ZMod.stdAddChar (1 : ZMod n) :=
    AddChar.map_add_eq_mul (ZMod.stdAddChar) i 1
  have e2 : ZMod.stdAddChar (i - 1) = ZMod.stdAddChar i * ZMod.stdAddChar (-1 : ZMod n) := by
    rw [← AddChar.map_add_eq_mul (ZMod.stdAddChar) i (-1)]
    ring_nf
  have e3 : ZMod.stdAddChar (-(1 : ZMod n)) = (starRingEnd ℂ) (ZMod.stdAddChar 1) :=
    (conj_stdAddChar 1).symm
  rw [e1, e2, e3]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [hc]
  ring

end Eigenvector

/-- A nonzero vector has positive squared norm. -/
