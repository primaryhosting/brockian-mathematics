import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex ZMod AddChar Matrix Finset

/-- The `N`-dimensional quantum Fourier transform matrix: the entry in row `j`, column `k` is
`exp (2 π i · j · k / N) / √N`, with rows and columns indexed by `ZMod N`. -/
noncomputable def qftMatrix (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun j k => (Real.sqrt N : ℂ)⁻¹ *
    Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val : ℕ) / N)

/-- The entries of the QFT matrix, expressed via the standard additive character of `ZMod N`
(`ZMod.stdAddChar`, which maps `j mod N` to `exp (2 π i j / N)`). -/
lemma qftMatrix_apply (N : ℕ) [NeZero N] (j k : ZMod N) :
    qftMatrix N j k = (Real.sqrt N : ℂ)⁻¹ * stdAddChar (j * k) := by
  have h : (((j.val * k.val : ℕ) : ℤ) : ZMod N) = j * k := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]; ring
  have h2 := ZMod.stdAddChar_coe (N := N) ((j.val * k.val : ℕ) : ℤ)
  rw [h] at h2
  rw [qftMatrix, h2]; push_cast; ring

/-- Complex conjugation of the standard additive character inverts its argument
(its values lie on the unit circle). -/
lemma conj_stdAddChar (N : ℕ) [NeZero N] (x : ZMod N) :
    starRingEnd ℂ (stdAddChar x) = stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (by simp [stdAddChar_apply])).symm

/-- Character orthogonality on `ZMod N`: `∑ m, e (m * t)` equals `N` if `t = 0` and `0` otherwise.
This is `AddChar.sum_mulShift` applied to the primitive character `ZMod.stdAddChar`. -/
lemma sum_stdAddChar_mul (N : ℕ) [NeZero N] (t : ZMod N) :
    ∑ m : ZMod N, stdAddChar (m * t) = if t = 0 then (N : ℂ) else 0 := by
  classical
  rw [AddChar.sum_mulShift t (isPrimitive_stdAddChar N)]
  simp [ZMod.card]

/-- The `N`-dimensional quantum Fourier transform matrix is unitary. -/
theorem qftMatrix_mem_unitaryGroup (N : ℕ) [NeZero N] :
    qftMatrix N ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN : (Real.sqrt N : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hsq : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNpos.le]; norm_cast
  have key : ∀ m : ZMod N, (star (qftMatrix N) j m) * qftMatrix N m k
      = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) * stdAddChar (m * (k - j)) := by
    intro m
    have hchar : stdAddChar (-(m * j)) * stdAddChar (m * k) = stdAddChar (m * (k - j)) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    simp only [qftMatrix_apply, star_def, map_mul, conj_stdAddChar]
    rw [show (starRingEnd ℂ) ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ by
      simp [← Complex.ofReal_inv]]
    linear_combination ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) * hchar
  rw [Finset.sum_congr rfl (fun m _ => key m), ← Finset.mul_sum, sum_stdAddChar_mul]
  by_cases h : j = k
  · subst h
    rw [sub_self, if_pos rfl, if_pos rfl]
    field_simp
    rw [sq, hsq]
  · rw [if_neg (by simpa [sub_eq_zero, eq_comm] using h), if_neg h, mul_zero]

/-- **The 7-qubit quantum Fourier transform matrix is unitary.**
It is the `2 ^ 7 = 128`-dimensional QFT matrix, acting on the state space of 7 qubits. -/
theorem qft_unitary_7 : qftMatrix (2 ^ 7) ∈ Matrix.unitaryGroup (ZMod (2 ^ 7)) ℂ :=
  qftMatrix_mem_unitaryGroup (2 ^ 7)

/-- Explicit form of unitarity for the 7-qubit QFT: `U† U = 1` and `U U† = 1`. -/
theorem qft_unitary_7' :
    star (qftMatrix (2 ^ 7)) * qftMatrix (2 ^ 7) = 1 ∧
      qftMatrix (2 ^ 7) * star (qftMatrix (2 ^ 7)) = 1 :=
  ⟨qft_unitary_7.1, qft_unitary_7.2⟩

end QC

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

