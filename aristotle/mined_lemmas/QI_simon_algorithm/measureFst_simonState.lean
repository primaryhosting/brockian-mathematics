/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/

theorem measureFst_simonState {n : ℕ} (f : Bits n → Bits n) (s : Bits n)
    (hf : SimonPromise f s) (y : Bits n) :
    measureFst (simonState f) y = if bdot y s = 0 then 2 / 2 ^ n else 0 := by
  classical
  have hexp : ∀ z : Bits n, ((Complex.normSq (simonState f (y, z)) : ℝ) : ℂ)
      = ((2:ℂ)^n)⁻¹ * ((2:ℂ)^n)⁻¹ *
        ∑ x : Bits n, ∑ x' : Bits n,
          ((if f x = z then (1:ℂ) else 0) * (if f x' = z then (1:ℂ) else 0)) *
            (sgn x y * sgn x' y) := by
    intro z
    rw [← Complex.mul_conj, simonState_apply]
    rw [map_mul, map_inv₀]
    have hconjpow : (starRingEnd ℂ) ((2:ℂ)^n) = (2:ℂ)^n := by
      rw [map_pow, Complex.conj_ofNat]
    rw [hconjpow, map_sum, mul_mul_mul_comm, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    refine Finset.sum_congr rfl ?_
    intro x' _
    rw [map_mul, conj_sgn]
    have hcz : (starRingEnd ℂ) (if f x' = z then (1:ℂ) else 0) = (if f x' = z then (1:ℂ) else 0) := by
      split <;> simp
    rw [hcz]
    ring
  have hswap : ∑ z : Bits n, ∑ x : Bits n, ∑ x' : Bits n,
        ((if f x = z then (1:ℂ) else 0) * (if f x' = z then (1:ℂ) else 0)) *
          (sgn x y * sgn x' y)
      = ∑ x : Bits n, ∑ x' : Bits n, (if f x = f x' then sgn x y * sgn x' y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro x' _
    rw [← Finset.sum_mul]
    by_cases hxx : f x = f x'
    · rw [if_pos hxx]
      have hone : ∑ z : Bits n, (if f x = z then (1:ℂ) else 0) * (if f x' = z then (1:ℂ) else 0)
          = 1 := by
        rw [Finset.sum_eq_single (f x)]
        · simp [hxx]
        · intro b _ hb
          simp [Ne.symm hb]
        · intro h; exact absurd (Finset.mem_univ (f x)) h
      rw [hone, one_mul]
    · rw [if_neg hxx]
      have hzero : ∑ z : Bits n, (if f x = z then (1:ℂ) else 0) * (if f x' = z then (1:ℂ) else 0)
          = 0 := by
        refine Finset.sum_eq_zero ?_
        intro z _
        by_cases h1 : f x = z
        · by_cases h2 : f x' = z
          · exact absurd (h1.trans h2.symm) hxx
          · simp [h2]
        · simp [h1]
      rw [hzero, zero_mul]
  have hpow : ((2:ℂ))^n ≠ 0 := pow_ne_zero n two_ne_zero
  have hcomplex : ((measureFst (simonState f) y : ℝ) : ℂ)
      = ((2:ℂ)^n)⁻¹ * (1 + sgn s y) := by
    rw [measureFst]
    push_cast
    rw [Finset.sum_congr rfl (fun z _ => hexp z), ← Finset.mul_sum, hswap,
      pair_sum f s hf y]
    field_simp
  rcases zmod_two_cases (bdot y s) with h | h
  · rw [if_pos h]
    have hsg : sgn s y = 1 := by
      simp [sgn, bdot_comm s y, h]
    rw [hsg] at hcomplex
    have : ((measureFst (simonState f) y : ℝ) : ℂ) = (((2 / 2 ^ n : ℝ)) : ℂ) := by
      rw [hcomplex]; push_cast; ring
    exact_mod_cast this
  · rw [if_neg (by rw [h]; decide)]
    have hsg : sgn s y = -1 := by
      simp [sgn, bdot_comm s y, h]
    rw [hsg] at hcomplex
    have : ((measureFst (simonState f) y : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
      rw [hcomplex]; push_cast; ring
    exact_mod_cast this

end QI

