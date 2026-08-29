import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

/-- The `n`-th (unnormalized) stationary state of a particle in an infinite square
well of width `L`: `ψₙ(x) = sin (n π x / L)`. -/

theorem particle_in_box (hbar m L : ℝ) (hL : 0 < L) (hm : 0 < m) :
    (∀ n : ℕ, 1 ≤ n →
        psi L n 0 = 0 ∧ psi L n L = 0 ∧
        (∃ x : ℝ, 0 < x ∧ x < L ∧ psi L n x ≠ 0) ∧
        (∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * deriv (deriv (psi L n)) x
            = energy hbar m L n * psi L n x) ∧
        energy hbar m L n = (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)) ∧
    (∀ k : ℝ, 0 < k →
        (Real.sin (k * L) = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ k = (n : ℝ) * Real.pi / L)) ∧
    (∀ (n : ℕ) (k : ℝ), k = (n : ℝ) * Real.pi / L →
        hbar ^ 2 * k ^ 2 / (2 * m) = energy hbar m L n) := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hm0 : m ≠ 0 := ne_of_gt hm
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
    refine ⟨?_, ?_, ?_, ?_, rfl⟩
    · simp [psi]
    · have h : (n : ℝ) * Real.pi * L / L = (n : ℝ) * Real.pi := by field_simp
      rw [psi, h, Real.sin_nat_mul_pi]
    · refine ⟨L / (2 * (n : ℝ)), by positivity, ?_, ?_⟩
      · rw [div_lt_iff₀ (by positivity)]
        nlinarith
      · have h : (n : ℝ) * Real.pi * (L / (2 * (n : ℝ))) / L = Real.pi / 2 := by
          field_simp
        rw [psi, h, Real.sin_pi_div_two]
        norm_num
    · intro x
      rw [deriv2_psi L n hL0, psi, energy]
      field_simp
  · intro k hk
    constructor
    · intro h
      rw [Real.sin_eq_zero_iff] at h
      obtain ⟨j, hj⟩ := h
      have hjpos : 0 < j := by
        by_contra hcon
        push_neg at hcon
        have hj0 : (j : ℝ) ≤ 0 := by exact_mod_cast hcon
        nlinarith [Real.pi_pos, mul_pos hk hL]
      refine ⟨j.toNat, by omega, ?_⟩
      have hcast : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
        have h1 : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (le_of_lt hjpos)
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
      rw [hcast, eq_div_iff hL0]
      linarith [hj]
    · rintro ⟨n, hn, rfl⟩
      have h : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by field_simp
      rw [h, Real.sin_nat_mul_pi]
  · rintro n k rfl
    rw [energy]
    field_simp

end QPhys

