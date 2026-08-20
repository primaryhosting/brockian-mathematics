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

theorem hadFst_normSq_sum {n : ℕ} (psi : Amp n) :
    ∑ p : Bits n × Bits n, Complex.normSq (hadFst psi p)
      = ∑ p : Bits n × Bits n, Complex.normSq (psi p) := by
  classical
  have hpow : ((2:ℂ))^n ≠ 0 := pow_ne_zero n two_ne_zero
  have hterm : ∀ y z : Bits n,
      ((Complex.normSq (hadFst psi (y, z)) : ℝ) : ℂ)
        = ((2:ℂ)^n)⁻¹ * ∑ x : Bits n, ∑ x' : Bits n,
            (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z))) := by
    intro y z
    rw [← Complex.mul_conj, hadFst]
    simp only []
    rw [map_mul, map_sum]
    have hc : (starRingEnd ℂ) (((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹)
        = ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    rw [hc, mul_mul_mul_comm, Finset.sum_mul_sum]
    have hcc : ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹
        = ((2:ℂ)^n)⁻¹ := by
      rw [← mul_inv, sqrt_two_pow_sq]
    rw [hcc]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    refine Finset.sum_congr rfl ?_
    intro x' _
    rw [map_mul, conj_sgn]
    ring
  have hz : ∀ z : Bits n,
      ∑ y : Bits n, ∑ x : Bits n, ∑ x' : Bits n,
        (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z)))
      = (2:ℂ)^n * ∑ x : Bits n, ((Complex.normSq (psi (x, z)) : ℝ) : ℂ) := by
    intro z
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [Finset.sum_comm]
    have hinner : ∀ x' : Bits n, ∑ y : Bits n,
        (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z)))
        = (if x = x' then (2:ℂ)^n else 0) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z))) := by
      intro x'
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_congr rfl (fun y _ => by rw [sgn_comm x y, sgn_comm x' y])]
      exact sgn_orthogonality x x'
    rw [Finset.sum_congr rfl (fun x' _ => hinner x'), Finset.sum_eq_single x]
    · rw [if_pos rfl, ← Complex.mul_conj]
    · intro b _ hb
      rw [if_neg (fun hc => hb hc.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ x) h
  have key : ((∑ p : Bits n × Bits n, Complex.normSq (hadFst psi p) : ℝ) : ℂ)
      = ((∑ p : Bits n × Bits n, Complex.normSq (psi p) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_sum, Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc ∑ y : Bits n, ∑ z : Bits n, ((Complex.normSq (hadFst psi (y, z)) : ℝ) : ℂ)
        = ∑ y : Bits n, ∑ z : Bits n, ((2:ℂ)^n)⁻¹ * ∑ x : Bits n, ∑ x' : Bits n,
            (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z))) :=
          Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => hterm y z))
      _ = ∑ z : Bits n, ∑ y : Bits n, ((2:ℂ)^n)⁻¹ * ∑ x : Bits n, ∑ x' : Bits n,
            (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z))) :=
          Finset.sum_comm
      _ = ∑ z : Bits n, ∑ x : Bits n, ((Complex.normSq (psi (x, z)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [← Finset.mul_sum, hz z, ← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
      _ = ∑ x : Bits n, ∑ z : Bits n, ((Complex.normSq (psi (x, z)) : ℝ) : ℂ) :=
          Finset.sum_comm
  exact_mod_cast key

/-- **The quantum query is unitary**: it preserves the total squared amplitude. -/
