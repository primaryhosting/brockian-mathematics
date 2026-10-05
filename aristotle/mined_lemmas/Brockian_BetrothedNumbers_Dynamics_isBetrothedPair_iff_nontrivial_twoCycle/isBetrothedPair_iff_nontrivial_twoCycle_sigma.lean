/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers.Dynamics

/-- The divisor-sum function `σ₁ n = ∑_{d ∣ n} d`, computed as the sum of all
divisors of `n` in `{0, 1, …, n}` (note `0 ∣ n` only when `n = 0`, in which case
the contribution is `0`, so `sigma1 0 = 0`).

This file is deliberately free of `import` statements, because the required
header comment must be the very first thing in the file and Lean does not allow
any command (including a module docstring) to precede `import`.  The companion
file `RequestProject/BetrothedNumbersMathlib.lean` proves that `sigma1` agrees
with Mathlib's `ArithmeticFunction.sigma 1` and restates the main theorem in
Mathlib's language. -/

theorem isBetrothedPair_iff_nontrivial_twoCycle_sigma (m n : ℕ) :
    (0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1) ↔
      (0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m - m - 1 = n ∧ sigma 1 n - n - 1 = m) := by
  have h := isBetrothedPair_iff_nontrivial_twoCycle m n
  rw [IsBetrothedPair] at h
  simpa [partner_eq, sigma1_eq_sigma] using h

end Brockian.BetrothedNumbers.Dynamics

