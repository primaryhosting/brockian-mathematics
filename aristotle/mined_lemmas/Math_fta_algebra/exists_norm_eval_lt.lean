/-
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Filter Topology

namespace Math

/-- Every nonzero complex number has an `n`-th root for `n > 0`
(elementary consequence of the surjectivity of `Complex.exp` onto `ℂ \ {0}`). -/

theorem exists_norm_eval_lt {p : ℂ[X]} (hp : 0 < p.degree) {z₀ : ℂ} (h0 : p.eval z₀ ≠ 0) :
    ∃ z : ℂ, ‖p.eval z‖ < ‖p.eval z₀‖ := by
  -- translate to `z₀ = 0`
  set r : ℂ[X] := p.comp (X + C z₀) with hr
  have hreval : ∀ w : ℂ, r.eval w = p.eval (w + z₀) := by
    intro w; simp [hr, eval_comp]
  have hr0 : r.eval 0 ≠ 0 := by simpa using (hreval 0).symm ▸ (by simpa using h0)
  have hrdeg : 0 < r.degree := by
    have h1 : (X + C z₀ : ℂ[X]).natDegree = 1 := by
      simp
    have : r.natDegree = p.natDegree := by
      rw [hr, natDegree_comp, h1, mul_one]
    have hpn : 0 < p.natDegree := natDegree_pos_iff_degree_pos.2 hp
    rw [← natDegree_pos_iff_degree_pos, this]
    exact hpn
  set a : ℂ := r.eval 0 with ha
  -- write `r = a * (1 + Xᵏ * t)` with `t(0) ≠ 0`
  set s : ℂ[X] := C a⁻¹ * r - 1 with hs
  have hs0 : s.eval 0 = 0 := by simp [hs, ← ha, inv_mul_cancel₀ hr0]
  have hsne : s ≠ 0 := by
    intro h
    have : C a⁻¹ * r = 1 := by
      have := h
      rw [hs, sub_eq_zero] at this
      exact this
    have hdeg : (C a⁻¹ * r).degree = 0 := by rw [this]; simp
    rw [degree_C_mul (by simpa using inv_ne_zero hr0)] at hdeg
    rw [hdeg] at hrdeg
    exact lt_irrefl _ hrdeg
  set k : ℕ := s.rootMultiplicity 0 with hk
  have hkpos : 0 < k := (rootMultiplicity_pos hsne).2 (by simpa [IsRoot] using hs0)
  set t : ℂ[X] := s /ₘ (X - C 0) ^ k with ht
  have hfact : (X : ℂ[X]) ^ k * t = s := by
    have := pow_mul_divByMonic_rootMultiplicity_eq s (0 : ℂ)
    simpa [ht, hk] using this
  have htc : t.eval 0 ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero (0 : ℂ) hsne
  obtain ⟨w, hw⟩ := exists_norm_one_add_pow_mul_lt t hkpos htc
  refine ⟨w + z₀, ?_⟩
  have hrw : r.eval w = a * (1 + w ^ k * t.eval w) := by
    have : r = C a * (1 + X ^ k * t) := by
      rw [hfact, hs, show (1 : ℂ[X]) + (C a⁻¹ * r - 1) = C a⁻¹ * r from by ring,
        ← mul_assoc, ← C_mul, mul_inv_cancel₀ hr0, C_1, one_mul]
    calc r.eval w = (C a * (1 + X ^ k * t)).eval w := by rw [← this]
      _ = a * (1 + w ^ k * t.eval w) := by simp
  have hane : ‖a‖ ≠ 0 := by simpa using hr0
  have : ‖r.eval w‖ < ‖a‖ := by
    rw [hrw, norm_mul]
    calc ‖a‖ * ‖1 + w ^ k * t.eval w‖ < ‖a‖ * 1 := by
          exact mul_lt_mul_of_pos_left hw (lt_of_le_of_ne (norm_nonneg a) (Ne.symm hane))
      _ = ‖a‖ := mul_one _
  rw [hreval w] at this
  simpa [ha, hreval 0] using this

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial has a root. -/
