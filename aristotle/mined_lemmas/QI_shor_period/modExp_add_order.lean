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

lemma modExp_add_order (n a k : ℕ) :
    modExp n a (k + orderOf (a : ZMod n)) = modExp n a k := by
  simp [modExp, pow_add, pow_orderOf_eq_one]

/-- Minimality: no positive number smaller than the order is a period. -/
