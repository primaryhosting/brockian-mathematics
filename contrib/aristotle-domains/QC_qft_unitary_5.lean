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

/-- The `N`-dimensional quantum Fourier transform matrix:
`(QFT_N)_{j,k} = exp(2πi·jk/N) / √N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / N) / (Real.sqrt N : ℝ)

/-- The geometric sum of `N`-th roots of unity: `∑_{k<N} exp(2πi·kd/N)` is `N` when `N ∣ d`
and `0` otherwise. -/
lemma sum_root_unity (N : ℕ) (hN : 0 < N) (d : ℤ) :
    ∑ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * d) / N)
      = if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = 2 * Real.pi * Complex.I * d / N := ⟨_, rfl⟩
  have hterm : ∀ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * d) / N)
      = Complex.exp z ^ (k : ℕ) := by
    intro k
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [hz]
    field_simp
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    ← Finset.sum_range fun i => Complex.exp z ^ i]
  have hzone : Complex.exp z = 1 ↔ (N : ℤ) ∣ d := by
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      rw [hz] at hn
      field_simp at hn
      exact ⟨n, by exact_mod_cast hn⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [hz, hn]
      push_cast
      field_simp
  by_cases h : (N : ℤ) ∣ d
  · simp [h, hzone.2 h, Finset.sum_const]
  · rw [if_neg h]
    have hne : Complex.exp z ≠ 1 := fun hc => h (hzone.1 hc)
    rw [geom_sum_eq hne]
    have hpow : Complex.exp z ^ N = 1 := by
      rw [← Complex.exp_nat_mul]
      have he : (N : ℂ) * z = (d : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hz]; field_simp
      rw [he]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I d
    rw [hpow]
    simp

/-- The `N`-dimensional QFT matrix is unitary for every `N > 0`. -/
theorem qft_unitary (N : ℕ) (hN : 0 < N) : qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  have hstar : ∀ a : ℕ,
      star (Complex.exp (2 * Real.pi * Complex.I * (a : ℕ) / N) / ((Real.sqrt N : ℝ) : ℂ))
        = Complex.exp (-(2 * Real.pi * Complex.I * (a : ℕ) / N)) / ((Real.sqrt N : ℝ) : ℂ) := by
    intro a
    simp [Complex.conj_ofReal, ← Complex.exp_conj, map_ofNat]
    ring_nf
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hkey : ∀ k : Fin N, (star (qftMatrix N)) j k * qftMatrix N k l
      = (1 / (N : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * ((l : ℕ) - (j : ℕ) : ℤ)) / N) := by
    intro k
    rw [Matrix.star_apply, qftMatrix]
    simp only [Matrix.of_apply]
    rw [hstar ((k : ℕ) * (j : ℕ)), div_mul_div_comm, ← Complex.exp_add, hsq, one_div,
      ← div_eq_inv_mul]
    congr 1
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => hkey k), ← Finset.mul_sum,
    sum_root_unity N hN ((l : ℕ) - (j : ℕ) : ℤ)]
  by_cases h : j = l
  · subst h
    simp [hN0]
  · have hne : ((l : ℕ) : ℤ) - (j : ℕ) ≠ 0 := by
      simp only [sub_ne_zero]
      intro hc
      exact h (Fin.ext (by exact_mod_cast hc.symm))
    have hnd : ¬ ((N : ℤ) ∣ ((l : ℕ) - (j : ℕ) : ℤ)) := by
      intro hd
      refine hne (Int.eq_zero_of_abs_lt_dvd hd ?_)
      have h1 := j.isLt
      have h2 := l.isLt
      rw [abs_lt]
      omega
    rw [if_neg hnd, if_neg h]
    ring

/-- The 5-qubit QFT matrix (dimension `2^5 = 32`) is unitary. -/
theorem qft_unitary_5 : qftMatrix (2 ^ 5) ∈ Matrix.unitaryGroup (Fin (2 ^ 5)) ℂ :=
  qft_unitary (2 ^ 5) (by norm_num)

end QC

