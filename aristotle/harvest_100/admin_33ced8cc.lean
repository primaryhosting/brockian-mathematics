/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced verbatim above; it is written as a plain block
-- comment rather than a `/-!` module docstring because Lean 4 does not allow a module
-- docstring to precede the `import` line.)

import Mathlib

namespace QC

open Complex Finset
open scoped Matrix

/-- The `n × n` quantum Fourier transform matrix: the entry in row `j`, column `k` is
`exp(2πi·j·k/n) / √n`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / n) / Real.sqrt n

/-- The root of unity `exp(2πi(j-k)/n)` appearing when multiplying row `j` of the QFT
matrix with the conjugate of row `k`. -/
noncomputable def qftRatio (n : ℕ) (j k : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((j : ℕ) : ℂ) - ((k : ℕ) : ℂ)) / n)

/-- Each term of the inner product of row `j` with row `k` is a power of `qftRatio`. -/
lemma entry_mul_conj (n : ℕ) (j k l : Fin n) :
    qftMatrix n j l * (starRingEnd ℂ) (qftMatrix n k l) = (qftRatio n j k) ^ (l : ℕ) / n := by
  have hs : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  unfold qftMatrix qftRatio
  rw [← Complex.exp_nat_mul, map_div₀, ← Complex.exp_conj, Complex.conj_ofReal,
    div_mul_div_comm, hs, ← Complex.exp_add]
  have hc : ((starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) * (l : ℕ) : ℕ) : ℂ) / n))
      = -(2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) * (l : ℕ) : ℕ) : ℂ) / n) := by
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hc]
  congr 2
  push_cast
  ring

/-- `qftRatio n j k` is an `n`-th root of unity. -/
lemma qftRatio_pow_n (n : ℕ) (hn : 0 < n) (j k : Fin n) : (qftRatio n j k) ^ n = 1 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold qftRatio
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨(j : ℕ) - (k : ℕ), ?_⟩
  push_cast
  field_simp

/-- `qftRatio n j k` equals `1` exactly on the diagonal. -/
lemma qftRatio_eq_one_iff (n : ℕ) (hn : 0 < n) (j k : Fin n) :
    qftRatio n j k = 1 ↔ j = k := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · intro h
    unfold qftRatio at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp at hm
    have h2 : ((j : ℕ) : ℂ) - ((k : ℕ) : ℂ) = (m : ℂ) * (n : ℂ) := by linear_combination hm
    have h3 : ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) = m * (n : ℤ) := by exact_mod_cast h2
    have hj := j.isLt
    have hk := k.isLt
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with h0 | h0 | h0
      · exfalso
        have : m * (n : ℤ) ≤ -(n : ℤ) := by nlinarith
        omega
      · exact h0
      · exfalso
        have : (n : ℤ) ≤ m * (n : ℤ) := by nlinarith
        omega
    rw [hm0] at h3
    simp at h3
    exact Fin.ext (by omega)
  · rintro rfl
    unfold qftRatio
    simp

/-- The `n × n` QFT matrix satisfies `U * Uᴴ = 1` for every `n > 0`. -/
lemma qft_mul_conjTranspose (n : ℕ) (hn : 0 < n) :
    qftMatrix n * (qftMatrix n)ᴴ = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have h1 : ∀ l : Fin n, qftMatrix n j l * (qftMatrix n)ᴴ l k
      = (qftRatio n j k) ^ (l : ℕ) / n := by
    intro l
    rw [Matrix.conjTranspose_apply]
    exact entry_mul_conj n j k l
  rw [Finset.sum_congr rfl (fun l _ => h1 l), ← Finset.sum_div]
  by_cases hjk : j = k
  · subst hjk
    have h : qftRatio n j j = 1 := (qftRatio_eq_one_iff n hn j j).2 rfl
    simp [h, Finset.card_univ, hn.ne']
  · have hne : qftRatio n j k ≠ 1 := fun h => hjk ((qftRatio_eq_one_iff n hn j k).1 h)
    have hsum : ∑ l : Fin n, (qftRatio n j k) ^ (l : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (qftRatio n j k) ^ i) n,
        geom_sum_eq hne, qftRatio_pow_n n hn j k]
      simp
    rw [hsum]
    simp [hjk]

/-- The 6-qubit QFT matrix (of size `2^6 = 64`) is unitary. -/
theorem qft_unitary_6 : qftMatrix (2 ^ 6) ∈ Matrix.unitaryGroup (Fin (2 ^ 6)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact qft_mul_conjTranspose _ (by positivity)

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

