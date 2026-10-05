import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open scoped BigOperators
open scoped Classical
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-! ## Betrothed (quasi-amicable) numbers -/

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers whose sums of divisors both equal `n + m + 1`, i.e. each is the sum of the
proper divisors, excluding `1`, of the other. -/

noncomputable def count (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun n => n ∈ A)).card

/-- `A` has asymptotic density zero. -/
