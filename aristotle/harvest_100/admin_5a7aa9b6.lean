import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
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

/-- The root of unity `exp (2 π i / N)`. -/
noncomputable def omega (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma omega_ne_zero (N : ℕ) : omega N ≠ 0 := Complex.exp_ne_zero _

lemma isPrimitiveRoot_omega {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (omega N) N := by
  have h := Complex.isPrimitiveRoot_exp N hN
  have : omega N = Complex.exp (2 * Real.pi * Complex.I / N) := rfl
  rw [this]
  convert h using 2

lemma conj_omega (N : ℕ) : (starRingEnd ℂ) (omega N) = (omega N)⁻¹ := by
  rw [omega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
    Complex.conj_natCast]
  ring

/-- The exponential entry of the (unnormalized) DFT matrix as a power of `omega N`. -/
lemma exp_entry (N a : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * a / N) = omega N ^ a := by
  rw [omega, ← Complex.exp_nat_mul]
  ring_nf

/-- Orthogonality of the rows of the DFT matrix. -/
lemma sum_omega_pow_mul_conj {N : ℕ} (hN : N ≠ 0) (j l : Fin N) :
    ∑ k : Fin N, omega N ^ ((j : ℕ) * (k : ℕ)) *
        (starRingEnd ℂ) (omega N ^ ((l : ℕ) * (k : ℕ))) =
      if j = l then (N : ℂ) else 0 := by
  have hne : omega N ^ (l : ℕ) ≠ 0 := pow_ne_zero _ (omega_ne_zero N)
  set z : ℂ := omega N ^ (j : ℕ) / omega N ^ (l : ℕ) with hz
  have h1 : (starRingEnd ℂ) (omega N ^ (l : ℕ)) = (omega N ^ (l : ℕ))⁻¹ := by
    rw [map_pow, conj_omega, inv_pow]
  have hterm : ∀ k : Fin N,
      omega N ^ ((j : ℕ) * (k : ℕ)) *
        (starRingEnd ℂ) (omega N ^ ((l : ℕ) * (k : ℕ))) = z ^ (k : ℕ) := by
    intro k
    rw [pow_mul, pow_mul, map_pow, h1, inv_pow, ← div_eq_mul_inv, hz, div_pow]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Fin.sum_univ_eq_sum_range (fun k => z ^ k) N]
  have hprim := isPrimitiveRoot_omega hN
  by_cases hjl : j = l
  · have hz1 : z = 1 := by rw [hz, hjl, div_self hne]
    simp [hz1, hjl]
  · have hzne : z ≠ 1 := by
      intro h
      rw [hz, div_eq_one_iff_eq hne] at h
      exact hjl (Fin.val_injective (hprim.pow_inj j.isLt l.isLt h))
    have hzN : z ^ N = 1 := by
      rw [hz, div_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) N, mul_comm (l : ℕ) N,
        pow_mul, pow_mul, hprim.pow_eq_one, one_pow, one_pow, div_one]
    rw [geom_sum_eq hzne, hzN]
    simp [hjl]

/-- The `n`-qubit quantum Fourier transform matrix:
`(QFT_n)_{j,k} = exp (2 π i j k / 2^n) / √(2^n)` acting on the `2^n`-dimensional
state space of `n` qubits. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / ((2 ^ n : ℕ) : ℂ)) /
      (Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ)

/-- **The n-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have hN : (2 ^ n : ℕ) ≠ 0 := by positivity
  have hNpos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
  have hsqrt : ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply]
  have hentry : ∀ a b : Fin (2 ^ n),
      qft n a b = omega (2 ^ n) ^ ((a : ℕ) * (b : ℕ)) /
        ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro a b
    rw [qft, Matrix.of_apply, exp_entry]
  have hstar : ∀ a b : Fin (2 ^ n),
      star (qft n) a b = (starRingEnd ℂ) (omega (2 ^ n) ^ ((b : ℕ) * (a : ℕ))) /
        ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro a b
    rw [Matrix.star_apply, hentry, RCLike.star_def, map_div₀, Complex.conj_ofReal]
  have hsum : ∑ k : Fin (2 ^ n), qft n j k * star (qft n) k l
      = (∑ k : Fin (2 ^ n), omega (2 ^ n) ^ ((j : ℕ) * (k : ℕ)) *
          (starRingEnd ℂ) (omega (2 ^ n) ^ ((l : ℕ) * (k : ℕ))))
        / (((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) *
            ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ)) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hentry, hstar]
    field_simp
  rw [hsum, sum_omega_pow_mul_conj hN j l]
  have hsq : ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ)
      = ((2 ^ n : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hNpos)]
    push_cast
    ring
  rw [hsq]
  by_cases hjl : j = l
  · simp [hjl, Matrix.one_apply]
  · simp [hjl]

end QC

