import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
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

set_option grind.warning false

namespace Frontier

open Complex

/-- A *trivial zero* of the Riemann zeta function is one of the points `-2, -4, -6, …`. -/

theorem isTrivialZero_of_re_nonpos {s : ℂ} (hz : riemannZeta s = 0) (hs : s.re ≤ 0) :
    IsTrivialZero s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact zeta_zero_ne_zero hz
  have hwre : 1 ≤ ((1 : ℂ) - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hw1 : (1 : ℂ) - s ≠ 1 := by
    intro h
    exact hs0 (by linear_combination -h)
  have heq := zeta_one_sub_of_re_pos (by linarith) hw1
  rw [show (1 : ℂ) - (1 - s) = s by ring, hz] at heq
  have hzw : riemannZeta (1 - s) ≠ 0 := zeta_ne_zero_of_one_le_re hwre
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : ((π : ℂ)) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hp : (2 * (π : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro h
    exact (mul_ne_zero two_ne_zero hpi) h.1
  have hcos : Complex.cos (π * (1 - s) / 2) = 0 := by
    rcases mul_eq_zero.mp heq.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h₃ | h₃
          · exact absurd h₃ two_ne_zero
          · exact absurd h₃ hp
        · exact absurd h'' hG
      · exact h'
    · exact absurd h hzw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hsk : s = -2 * (k : ℂ) := by
    field_simp at hk
    linear_combination -hk
  have hkre : ((k : ℝ)) ≥ 0 := by
    have : s.re = -2 * (k : ℝ) := by
      rw [hsk]; simp
    rw [this] at hs
    linarith
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hsk
    exact hs0 hsk
  have hk1 : 1 ≤ k := by
    have : (0 : ℤ) ≤ k := by exact_mod_cast hkre
    omega
  refine ⟨(k - 1).toNat, ?_⟩
  have : ((((k - 1).toNat : ℕ) : ℂ)) = (k : ℂ) - 1 := by
    have : (((k - 1).toNat : ℤ)) = k - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) this
  rw [hsk, this]
  ring

/-- **Left edge of the critical strip.** Every nontrivial zero has positive real part. -/
