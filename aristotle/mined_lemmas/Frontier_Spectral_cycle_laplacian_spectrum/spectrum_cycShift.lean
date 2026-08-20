import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Polynomial Matrix Complex

variable (n : ℕ) [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `(S *ᵥ v) i = v (i + 1)`. -/

lemma spectrum_cycShift : spectrum ℂ (cycShift n) = {z : ℂ | z ^ n = 1} := by
  ext z
  rw [mem_spectrum_iff_exists_eigenvector]
  constructor
  · rintro ⟨v, hv, h⟩
    have hpow := pow_mulVec_of_eigen n h n
    rw [cycShift_pow_card, Matrix.one_mulVec] at hpow
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have h2 := congrFun hpow i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2 hi
    have : (z ^ n - 1) * v i = 0 := by rw [sub_mul, one_mul, ← h2]; ring
    rcases mul_eq_zero.mp this with h3 | h3
    · simpa [sub_eq_zero] using h3
    · exact absurd h3 hi
  · intro hz
    simp only [Set.mem_setOf_eq] at hz
    refine ⟨fun i => z ^ (i.val), ?_, ?_⟩
    · intro h
      have h0 := congrFun h (0 : ZMod n)
      simp only [ZMod.val_zero, pow_zero, Pi.zero_apply] at h0
      exact one_ne_zero h0
    · funext i
      rw [cycShift_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul]
      have : z ^ ((i + 1).val) = z ^ (i.val + 1) := by
        refine pow_eq_pow_of_natCast_eq n hz ?_
        push_cast [ZMod.natCast_val, ZMod.cast_id]
        ring
      rw [this, pow_succ, mul_comm]

