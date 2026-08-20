import Mathlib

namespace Brockian.MsGaussSum

open Finset Complex

/-- The summand `exp (2πi k²/p)` is the value of the standard additive character at `k²`. -/

private lemma exp_eq_stdAddChar (p : ℕ) [NeZero p] (k : ZMod p) :
    Complex.exp (2 * Real.pi * Complex.I * ((k.val : ℂ) ^ 2) / (p : ℂ))
      = ZMod.stdAddChar (k ^ 2) := by
  simp [ZMod.stdAddChar]
  rw [ZMod.toCircle_apply]
  rw [Complex.exp_eq_exp_iff_exists_int]
  have h : (k ^ 2).val ≡ k.val ^ 2 [MOD p] := by
    simp [Nat.ModEq]
    have h2 : ((k.val ^ 2) : ZMod p) = k ^ 2 := by simp
    have h3 : (k ^ 2).val = ((k.val : ZMod p) ^ 2).val := by rw [h2]
    have h4 : ((k.val : ZMod p) ^ 2).val = ((k.val ^ 2 : ℕ) : ZMod p).val := by
      rw [← Nat.cast_pow]
    rw [h3, h4, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_refl p)]
  have h' : (p : ℤ) ∣ (k.val ^ 2 - (k ^ 2).val) := h.dvd
  obtain ⟨n, hn⟩ := h'
  use n
  have hk : (k.val : ℤ) ^ 2 = (k ^ 2).val + p * n := by linarith
  have hk' : (k.val : ℂ) ^ 2 = (k ^ 2).val + p * (n : ℂ) := by exact_mod_cast hk
  have hk'' : k.cast ^ 2 = (k ^ 2).val + p * (n : ℂ) := by
    have : k.cast = (k.val : ℂ) := by simp only [ZMod.natCast_val]
    rw [this]
    exact hk'
  rw [hk'']
  field_simp [NeZero.ne p]

/-- Complex conjugation of the standard additive character. -/
