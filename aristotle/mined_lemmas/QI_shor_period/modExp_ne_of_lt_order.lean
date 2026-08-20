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

lemma modExp_ne_of_lt_order {n a p : ℕ} (hp : 0 < p) (hlt : p < orderOf (a : ZMod n)) :
    modExp n a p ≠ modExp n a 0 := by
  intro hcon
  simp only [modExp, pow_zero] at hcon
  exact (pow_ne_one_of_lt_orderOf hp.ne' hlt) hcon

/-- Exact characterization of the periods of `k ↦ a ^ k mod n`: they are the multiples
of the order. -/
