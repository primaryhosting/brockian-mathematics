import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate `m = (2^k - 1) * (p + 2)`. -/

theorem sigmaCriterion_rhs_eq (k p : ℕ) :
    (2 ^ (k + 1) - 1) * (p + 1) = thabitCandidate k p + thabitPartner k p + 1 := by
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ k = a + 1 :=
    ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  simp only [thabitCandidate, thabitPartner, pow_succ, ha, Nat.add_sub_cancel]
  have h : (a + 1) * 2 - 1 = 2 * a + 1 := by omega
  rw [h]
  ring

/-- The sigma criterion says precisely that `σ(m) = m + n + 1`, i.e. that `m` satisfies the
betrothed-number condition relative to its Thabit partner `n`. -/
