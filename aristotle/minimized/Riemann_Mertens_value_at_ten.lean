import Mathlib
/-!
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Mertens

open ArithmeticFunction

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, where `μ` is Mathlib's Möbius function
`ArithmeticFunction.moebius`. -/

def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius k

/-- `M 10 = ∑_{k=1}^{10} μ k = -1`. -/
