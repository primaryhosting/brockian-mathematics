import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- The adjacency matrix of the cycle graph `C₁₃` (the Hückel matrix of the
`C₁₃` carbon ring, in units where `α = 0` and `β = 1`). -/

lemma U_mul_V : U * V = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  set x : ℂ := om ^ (j : ℕ) * (om ^ (j' : ℕ))⁻¹ with hx
  have hterm : ∀ k : Fin 13, U j k * V k j' = (13 : ℂ)⁻¹ * x ^ (k : ℕ) := by
    intro k
    rw [U_apply, V, vec, zeta, ← pow_mul, ← pow_mul, Nat.mul_comm (k : ℕ) (j' : ℕ), hx,
      mul_pow, inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  have hsum : ∑ k : Fin 13, x ^ (k : ℕ) = ∑ k ∈ Finset.range 13, x ^ k :=
    Fin.sum_univ_eq_sum_range (fun k => x ^ k) 13
  rw [hsum]
  by_cases hjj : j = j'
  · subst hjj
    have hx1 : x = 1 := by
      rw [hx, mul_inv_cancel₀ (pow_ne_zero _ om_ne_zero)]
    rw [hx1]
    simp [Matrix.one_apply_eq]
  · have hx1 : x ≠ 1 := by
      intro h
      apply hjj
      have h' : om ^ (j : ℕ) = om ^ (j' : ℕ) := by
        rw [hx, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ om_ne_zero)] at h
        exact h
      exact Fin.ext (om_primitive.pow_inj j.isLt j'.isLt h')
    have hpow : ∀ m : ℕ, (om ^ m) ^ 13 = 1 := by
      intro m
      rw [← pow_mul, Nat.mul_comm, pow_mul, om_pow13, one_pow]
    have hx13 : x ^ 13 = 1 := by
      rw [hx, mul_pow, inv_pow, hpow, hpow, inv_one, mul_one]
    rw [geom_sum_eq hx1 13, hx13]
    simp [Matrix.one_apply_ne hjj]

