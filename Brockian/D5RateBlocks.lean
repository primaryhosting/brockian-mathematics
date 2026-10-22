import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Two-dimensional blocks for symmetric dihedral rates

The off-diagonal Hermitian block `Q C` commutes with `Q D` exactly when
`C * conj D` is real. This criterion includes zero symbols and negative real
proportionality: it does not require two nonzero complex numbers to have the
same oriented phase.
-/

open Matrix Complex

namespace Brockian.D5RateBlocks

local notation "conjC" => (starRingEnd ℂ)

/-- The Hermitian reflection block in a paired Fourier basis. -/
def Q (C : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, C; conjC C, 0]

theorem Q_conjTranspose (C : ℂ) : (Q C).conjTranspose = Q C := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q, Matrix.conjTranspose_apply]

theorem Q_mul (C D : ℂ) :
    Q C * Q D = !![C * conjC D, 0; 0, conjC C * D] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, Matrix.mul_apply, Fin.sum_univ_two]

/-- The complex cross-product criterion, with no nonzero assumptions. -/
theorem cross_eq_iff_im_zero (C D : ℂ) :
    C * conjC D = D * conjC C ↔ (C * conjC D).im = 0 := by
  constructor
  · intro h
    have hi := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at hi ⊢
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h ⊢
      linarith

theorem Q_mul_comm_iff_cross_eq (C D : ℂ) :
    Q C * Q D = Q D * Q C ↔ C * conjC D = D * conjC C := by
  constructor
  · intro h
    simpa [Q_mul] using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  · intro h
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Q_mul] using h
    · simp [Q_mul]
    · simp [Q_mul]
    · simpa [Q_mul, mul_comm] using h.symm

/-- Exact commutation criterion for the two reflection blocks. -/
theorem Q_mul_comm_iff (C D : ℂ) :
    Q C * Q D = Q D * Q C ↔ (C * conjC D).im = 0 := by
  rw [Q_mul_comm_iff_cross_eq, cross_eq_iff_im_zero]

theorem Q_commute_iff (C D : ℂ) :
    Commute (Q C) (Q D) ↔ (C * conjC D).im = 0 :=
  Q_mul_comm_iff C D

/-- Equivalent real-coordinate determinant test. -/
theorem Q_commute_iff_det_zero (C D : ℂ) :
    Commute (Q C) (Q D) ↔ C.re * D.im - C.im * D.re = 0 := by
  rw [Q_commute_iff]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  constructor <;> intro h <;> linarith

/-- Zero symbols commute with every reflection block. -/
theorem Q_zero_commute (C : ℂ) : Commute (Q 0) (Q C) := by
  rw [Q_commute_iff]
  simp

/-- Real proportionality suffices, including negative proportionality. -/
theorem Q_real_multiple_commute (t : ℝ) (C : ℂ) :
    Commute (Q C) (Q ((t : ℂ) * C)) := by
  rw [Q_commute_iff]
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Antiparallel complex symbols are an allowed commuting case. -/
theorem Q_neg_commute (C : ℂ) : Commute (Q C) (Q (-C)) := by
  simpa using Q_real_multiple_commute (-1) C

/-- A scalar diagonal part minus the Hermitian reflection block. -/
def rateBlock (d C : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![d, -C; -conjC C, d]

theorem rateBlock_eq (d C : ℂ) : rateBlock d C = d • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Q C := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rateBlock, Q]

theorem rateBlock_mul (d e C D : ℂ) :
    rateBlock d C * rateBlock e D =
      !![d * e + C * conjC D, -(d * D + C * e);
         -(conjC C * e + d * conjC D), conjC C * D + d * e] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rateBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Scalar diagonal terms do not change the exact commutation criterion. -/
theorem rateBlock_mul_comm_iff (d e C D : ℂ) :
    rateBlock d C * rateBlock e D = rateBlock e D * rateBlock d C ↔
      (C * conjC D).im = 0 := by
  rw [← cross_eq_iff_im_zero]
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    have hdiag : d * e + C * conjC D = e * d + D * conjC C := by
      simpa [rateBlock_mul] using h00
    calc
      C * conjC D = (d * e + C * conjC D) - d * e := by ring
      _ = (e * d + D * conjC C) - d * e := by rw [hdiag]
      _ = D * conjC C := by ring
  · intro h
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [rateBlock_mul, mul_comm] using congrArg (fun z : ℂ => d * e + z) h
    · simp [rateBlock_mul]
      ring
    · simp [rateBlock_mul]
      ring
    · simpa [rateBlock_mul, mul_comm] using congrArg (fun z : ℂ => z + d * e) h.symm

theorem rateBlock_commute_iff (d e C D : ℂ) :
    Commute (rateBlock d C) (rateBlock e D) ↔ (C * conjC D).im = 0 :=
  rateBlock_mul_comm_iff d e C D

end Brockian.D5RateBlocks
