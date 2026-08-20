import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- The modular exponentiation function `k ↦ a ^ k mod n`, the function whose period
Shor's algorithm computes. -/

def modExp (n a k : ℕ) : ZMod n := (a : ZMod n) ^ k

/-- If `a` is coprime to `n` then `a` has finite multiplicative order in `ZMod n`. -/

lemma modExp_period_iff (n a p : ℕ) :
    (∀ k, modExp n a (k + p) = modExp n a k) ↔ orderOf (a : ZMod n) ∣ p := by
  constructor
  · intro hper
    have h0 := hper 0
    simp only [modExp, zero_add, pow_zero] at h0
    exact orderOf_dvd_of_pow_eq_one h0
  · rintro ⟨c, rfl⟩ k
    simp [modExp, pow_add, pow_mul, pow_orderOf_eq_one]

/-- Continued-fraction recovery step: from an exact rational `s / r` with `s` coprime to
the period `r`, the denominator recovered in lowest terms is exactly `r`. -/
