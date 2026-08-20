/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
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

namespace QC

open Complex Finset

/-- The `N × N` quantum Fourier transform matrix, with rows and columns indexed by `ZMod N`:
its `(j, k)` entry is `N ^ (-1/2) * exp (2 π i j k / N)`.  For `N = 2 ^ n` this is the QFT on
`n` qubits (with computational basis states identified with residues mod `2 ^ n`). -/

theorem qft_unitary (N : ℕ) [NeZero N] : qftMatrix N ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hsq : ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : ZMod N, qftMatrix N j k * (star (qftMatrix N)) k l
      = (N : ℂ)⁻¹ * ZMod.stdAddChar ((j - l) * k) := by
    intro k
    rw [Matrix.star_apply, qftMatrix_apply, qftMatrix_apply]
    simp only [star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal, conj_stdAddChar]
    rw [show (j - l) * k = j * k + -(l * k) by ring, AddChar.map_add_eq_mul, ← hsq]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, sum_stdAddChar, Matrix.one_apply]
  simp only [sub_eq_zero]
  split_ifs with h
  · rw [inv_mul_cancel₀ hN]
  · rw [mul_zero]

/-- The 7-qubit quantum Fourier transform matrix (of size `2 ^ 7 = 128`) is unitary. -/
