/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The `N × N` discrete (quantum) Fourier transform matrix: its `(j, k)` entry is
`N^(-1/2) * exp (2 π i j k / N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    (Real.sqrt N : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / N)

/-- The quantum Fourier transform matrix on `n` qubits, of size `2^n × 2^n`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qftMatrix (2 ^ n)

section General

variable {N : ℕ}

/-- The `N`-th root of unity `exp (2 π i / N)` used by the QFT. -/
noncomputable def zetaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

theorem isPrimitiveRoot_zetaN (hN : N ≠ 0) : IsPrimitiveRoot (zetaN N) N := by
  have := Complex.isPrimitiveRoot_exp N hN
  simpa [zetaN, mul_assoc] using this

theorem norm_zetaN : ‖zetaN N‖ = 1 := by
  have h : zetaN N = Complex.exp ((2 * Real.pi / N : ℝ) * Complex.I) := by
    rw [zetaN]
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem zetaN_ne_zero : zetaN N ≠ 0 := Complex.exp_ne_zero _

theorem qftMatrix_apply (j k : Fin N) :
    qftMatrix N j k = (Real.sqrt N : ℂ)⁻¹ * zetaN N ^ (j.val * k.val) := by
  rw [qftMatrix]
  simp only [Matrix.of_apply]
  congr 1
  rw [zetaN, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Orthogonality relation for the powers of `zetaN N`. -/
theorem sum_zeta_orthogonality (hN : N ≠ 0) (a b : Fin N) :
    (∑ j : Fin N, ((zetaN N)⁻¹ ^ a.val * zetaN N ^ b.val) ^ j.val) =
      if a = b then (N : ℂ) else 0 := by
  set w : ℂ := (zetaN N)⁻¹ ^ a.val * zetaN N ^ b.val with hw
  have hzeta := isPrimitiveRoot_zetaN (N := N) hN
  have hpowN : zetaN N ^ N = 1 := hzeta.pow_eq_one
  have hwN : w ^ N = 1 := by
    rw [hw, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val N, mul_comm b.val N, pow_mul, pow_mul,
      hpowN, inv_pow, hpowN]
    simp
  have hinv : ∀ m : ℕ, (zetaN N)⁻¹ ^ m * zetaN N ^ m = 1 := by
    intro m
    rw [← mul_pow, inv_mul_cancel₀ (zetaN_ne_zero (N := N)), one_pow]
  by_cases hab : a = b
  · subst hab
    have hw1 : w = 1 := hinv a.val
    simp [hw1]
  · have hwne : w ≠ 1 := by
      intro h
      apply hab
      have h2 : zetaN N ^ b.val = zetaN N ^ a.val := by
        calc zetaN N ^ b.val = (zetaN N)⁻¹ ^ a.val * zetaN N ^ b.val * zetaN N ^ a.val := by
              rw [mul_comm ((zetaN N)⁻¹ ^ a.val) (zetaN N ^ b.val), mul_assoc, hinv a.val, mul_one]
          _ = 1 * zetaN N ^ a.val := by rw [← hw, h]
          _ = zetaN N ^ a.val := one_mul _
      exact (Fin.ext (hzeta.pow_inj b.isLt a.isLt h2)).symm
    have hrange : (∑ j : Fin N, w ^ j.val) = ∑ i ∈ Finset.range N, w ^ i := by
      rw [Finset.sum_range fun i => w ^ i]
    rw [hrange, geom_sum_eq hwne, hwN]
    simp [hab]

/-- The `N × N` QFT matrix is unitary for every `N ≠ 0`. -/
theorem qftMatrix_unitary (hN : N ≠ 0) : qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hsq : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ * (N : ℂ) = 1 := by
    have h1 : (Real.sqrt N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hne : (Real.sqrt N : ℂ) ≠ 0 := by
      have : Real.sqrt N ≠ 0 := by positivity
      exact_mod_cast this
    have h2 : ((Real.sqrt N : ℂ)) ^ 2 = (N : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) h1
      push_cast at this
      exact this
    rw [← h2]
    field_simp
  have hconj : (starRingEnd ℂ) (zetaN N) = (zetaN N)⁻¹ :=
    (Complex.inv_eq_conj (norm_zetaN (N := N))).symm
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hentry : ∀ j : Fin N, (star (qftMatrix N)) a j * qftMatrix N j b =
      ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ *
        ((zetaN N)⁻¹ ^ a.val * zetaN N ^ b.val) ^ j.val := by
    intro j
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, qftMatrix_apply,
      qftMatrix_apply]
    rw [show star ((Real.sqrt N : ℂ)⁻¹ * zetaN N ^ (j.val * a.val))
        = (starRingEnd ℂ) ((Real.sqrt N : ℂ)⁻¹ * zetaN N ^ (j.val * a.val)) from rfl]
    rw [show (starRingEnd ℂ) ((Real.sqrt N : ℂ)⁻¹ * zetaN N ^ (j.val * a.val))
        = (Real.sqrt N : ℂ)⁻¹ * (zetaN N)⁻¹ ^ (j.val * a.val) by
      rw [map_mul, map_pow, hconj,
        show (starRingEnd ℂ) ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ by
          simp [← Complex.ofReal_inv]]]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val j.val, mul_comm b.val j.val]
    ring
  rw [Finset.sum_congr rfl fun j _ => hentry j, ← Finset.mul_sum,
    sum_zeta_orthogonality hN a b]
  by_cases hab : a = b
  · simp [hab, hsq]
  · simp [hab]

end General

/-- **The 8-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_8 : qft 8 ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qftMatrix_unitary (by norm_num)

end QC

