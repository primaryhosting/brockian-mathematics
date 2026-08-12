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

namespace QC

/-- The `N × N` Quantum Fourier Transform matrix:
`(QFT N) j k = exp (2 π i j k / N) / √N`. -/
noncomputable def qft (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => Complex.exp (2 * Real.pi * Complex.I * (j * k) / N) / Real.sqrt N

section
variable {N : ℕ}

/-- The `(a, b)` "phase" of the QFT: `exp (2 π i (b - a) / N)`. -/
private noncomputable def phase (N : ℕ) (a b : Fin N) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((b : ℕ) - (a : ℕ)) / N)

private lemma star_qft_mul_qft (hN : N ≠ 0) (a b j : Fin N) :
    star (qft N j a) * qft N j b = (1 / (N : ℂ)) * (phase N a b) ^ (j : ℕ) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h1 : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  rw [show star (qft N j a)
        = Complex.exp (-(2 * Real.pi * Complex.I * (j * a) / N)) / Real.sqrt N by
    simp [qft, ← Complex.exp_conj, Complex.conj_I, map_ofNat]; ring_nf]
  rw [phase, ← Complex.exp_nat_mul]
  simp only [qft, Matrix.of_apply, div_mul_div_comm, ← Complex.exp_add]
  rw [h1, one_div, ← div_eq_inv_mul]
  congr 1
  ring_nf

private lemma phase_pow_card (hN : N ≠ 0) (a b : Fin N) : (phase N a b) ^ N = 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [phase, ← Complex.exp_nat_mul]
  rw [show (N : ℂ) * (2 * Real.pi * Complex.I * ((b : ℕ) - (a : ℕ)) / N)
        = (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) : ℤ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I _

private lemma phase_ne_one (hN : N ≠ 0) {a b : Fin N} (hab : a ≠ b) : phase N a b ≠ 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  intro h
  rw [phase, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc : ((b : ℕ) : ℂ) - ((a : ℕ) : ℂ) = (n : ℂ) * N := by
    field_simp at hn
    linear_combination hn
  have hz : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = n * N := by exact_mod_cast hc
  have h1 : ((a : ℕ) : ℤ) < N := by exact_mod_cast a.isLt
  have h2 : ((b : ℕ) : ℤ) < N := by exact_mod_cast b.isLt
  have h3 : (0 : ℤ) ≤ ((a : ℕ) : ℤ) := Int.natCast_nonneg _
  have h4 : (0 : ℤ) ≤ ((b : ℕ) : ℤ) := Int.natCast_nonneg _
  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hlt | heq | hgt
    · nlinarith [Int.lt_iff_add_one_le.mp hlt]
    · exact heq
    · nlinarith [Int.lt_iff_add_one_le.mp hgt]
  rw [hn0, zero_mul] at hz
  have hEq : ((b : ℕ) : ℤ) = ((a : ℕ) : ℤ) := by linarith
  have : (b : ℕ) = (a : ℕ) := by exact_mod_cast hEq
  exact hab (Fin.ext this).symm

private lemma phase_self (a : Fin N) : phase N a a = 1 := by
  simp [phase]

/-- The QFT matrix is an isometry: `(QFT N)ᴴ * (QFT N) = 1`. -/
theorem qft_conjTranspose_mul_self (hN : N ≠ 0) :
    (qft N).conjTranspose * qft N = 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  ext a b
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin N, (qft N).conjTranspose a j * qft N j b
      = (1 / (N : ℂ)) * (phase N a b) ^ (j : ℕ) := by
    intro j
    rw [Matrix.conjTranspose_apply]
    exact star_qft_mul_qft hN a b j
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun i => (phase N a b) ^ i) N]
  by_cases hab : a = b
  · subst hab
    rw [phase_self a]
    simp [hN']
  · rw [geom_sum_eq (phase_ne_one hN hab), phase_pow_card hN]
    simp [hab]

/-- The QFT matrix is unitary. -/
theorem qft_mem_unitaryGroup (hN : N ≠ 0) :
    qft N ∈ Matrix.unitaryGroup (Fin N) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (qft_conjTranspose_mul_self hN)

end

/-- The `8 × 8` QFT matrix (the QFT on 3 qubits) is unitary. -/
theorem qft_unitary_8 : qft 8 ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  qft_mem_unitaryGroup (by norm_num)

/-- The QFT matrix on 8 qubits (dimension `2 ^ 8 = 256`) is unitary. -/
theorem qft_unitary_8_qubits : qft (2 ^ 8) ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qft_mem_unitaryGroup (by norm_num)

end QC

