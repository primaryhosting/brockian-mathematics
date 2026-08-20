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

namespace QC

open Complex

/-- The primitive `N`-th root of unity `exp (2πi/N)` used in the quantum Fourier transform. -/

theorem qft_unitary (N : ℕ) (hN : N ≠ 0) : qft N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hprim : IsPrimitiveRoot (qftOmega N) N := Complex.isPrimitiveRoot_exp N hN
  have hpow : qftOmega N ^ N = 1 := hprim.pow_eq_one
  have hne : qftOmega N ≠ 0 := qftOmega_ne_zero N
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNR.le]
    norm_cast
  have hsne : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨x, hxdef⟩ : ∃ x : ℂ, x = qftOmega N ^ (k : ℕ) * (qftOmega N ^ (j : ℕ))⁻¹ := ⟨_, rfl⟩
  have hterm : ∀ l : Fin N, (star (qft N)) j l * qft N l k = x ^ (l : ℕ) / (N : ℂ) := by
    intro l
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, qft_apply, qft_apply,
      star_div₀, star_pow, conj_qftOmega, Complex.star_def, Complex.conj_ofReal, hxdef, ← hs]
    field_simp
    ring
  have hxN : x ^ N = 1 := by
    have h1 : (qftOmega N ^ (k : ℕ)) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
    have h2 : (qftOmega N ^ (j : ℕ)) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
    rw [hxdef, mul_pow, inv_pow, h1, h2, inv_one, mul_one]
  have hx1 : x = 1 ↔ j = k := by
    constructor
    · intro h
      rw [hxdef] at h
      have hkj : qftOmega N ^ (k : ℕ) = qftOmega N ^ (j : ℕ) := by
        field_simp at h
        exact h
      exact (Fin.ext (hprim.pow_inj k.isLt j.isLt hkj)).symm
    · rintro rfl
      rw [hxdef]
      field_simp
  calc ∑ l : Fin N, (star (qft N)) j l * qft N l k
      = ∑ l : Fin N, x ^ (l : ℕ) / (N : ℂ) := Finset.sum_congr rfl (fun l _ => hterm l)
    _ = (∑ l ∈ Finset.range N, x ^ l) / (N : ℂ) := by
        rw [Finset.sum_div, Fin.sum_univ_eq_sum_range (fun l => x ^ l / (N : ℂ))]
    _ = (if x = 1 then (N : ℂ) else 0) / (N : ℂ) := by rw [sum_pow_of_pow_eq_one hxN]
    _ = if j = k then 1 else 0 := by
        by_cases h : j = k
        · rw [if_pos (hx1.mpr h), if_pos h, div_self hNC]
        · rw [if_neg (fun hc => h (hx1.mp hc)), if_neg h, zero_div]

/-- **The 4-qubit quantum Fourier transform matrix is unitary.**
Four qubits span a `2^4 = 16`-dimensional Hilbert space. -/
