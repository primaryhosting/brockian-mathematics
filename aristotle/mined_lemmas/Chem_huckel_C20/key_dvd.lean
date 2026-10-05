import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

lemma key_dvd : (X ^ 20 - 1 : ℂ[X]) ∣ pt.comp (X + X ^ 19) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  set I : Ideal ℂ[X] := Ideal.span {(X ^ 20 - 1 : ℂ[X])} with hI
  set φ := Ideal.Quotient.mk I with hphi
  have hzero : φ (X ^ 20 - 1) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  set x := φ X with hx
  have hx20 : x ^ 20 = 1 := by
    have h : φ (X ^ 20) - φ (1 : ℂ[X]) = 0 := by rw [← map_sub]; exact hzero
    rw [map_pow, map_one, ← hx, sub_eq_zero] at h
    exact h
  have hfact : ∏ k ∈ range 20, (x - φ (C (w ^ k))) = 0 := by
    have h1 : (X ^ 20 - C 1 : ℂ[X]) = ∏ k ∈ range 20, (X - C (w ^ k * 1)) :=
      X_pow_sub_C_eq_prod w_primitive (by norm_num) (one_pow 20)
    have h2 : φ (X ^ 20 - C 1) = 0 := by rw [C_1]; exact hzero
    rw [h1, map_prod] at h2
    rw [← h2]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [mul_one, map_sub, ← hx]
  have hcomp : pt.comp (X + X ^ 19) =
      ∏ k ∈ range 20, ((X + X ^ 19) - C (w ^ k + w ^ (20 - k))) := by
    rw [pt, Polynomial.prod_comp]
    simp
  rw [hcomp, map_prod]
  have hy : ∀ k ∈ range 20, φ (C (w ^ k)) * φ (C (w ^ (20 - k))) = 1 := by
    intro k hk
    have hk' : k ≤ 20 := by have := Finset.mem_range.mp hk; omega
    rw [← map_mul, ← C_mul, ← pow_add, Nat.add_sub_cancel' hk', w_pow_twenty, C_1, map_one]
  have hstep : ∀ k ∈ range 20,
      x * (φ (X + X ^ 19 - C (w ^ k + w ^ (20 - k))))
        = (x - φ (C (w ^ k))) * (x - φ (C (w ^ (20 - k)))) := by
    intro k hk
    have h := hy k hk
    rw [C_add, map_sub, map_add, map_add, map_pow, ← hx]
    linear_combination hx20 - h
  calc ∏ k ∈ range 20, φ (X + X ^ 19 - C (w ^ k + w ^ (20 - k)))
      = (∏ _k ∈ range 20, x) * ∏ k ∈ range 20, φ (X + X ^ 19 - C (w ^ k + w ^ (20 - k))) := by
        rw [Finset.prod_const, card_range, hx20, one_mul]
    _ = ∏ k ∈ range 20, (x * φ (X + X ^ 19 - C (w ^ k + w ^ (20 - k)))) := by
        rw [Finset.prod_mul_distrib]
    _ = ∏ k ∈ range 20, ((x - φ (C (w ^ k))) * (x - φ (C (w ^ (20 - k))))) :=
        Finset.prod_congr rfl hstep
    _ = (∏ k ∈ range 20, (x - φ (C (w ^ k)))) * ∏ k ∈ range 20, (x - φ (C (w ^ (20 - k)))) := by
        rw [Finset.prod_mul_distrib]
    _ = 0 := by rw [hfact, zero_mul]

/-- `pt` annihilates the adjacency matrix. -/
