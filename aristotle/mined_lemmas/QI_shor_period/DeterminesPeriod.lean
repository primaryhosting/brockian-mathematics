import Mathlib
/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Finset Complex

/-!
## The Shor sampling distribution

We model the period-finding core of Shor's algorithm.  Fix a modulus `N`, a unit
`u : (ZMod N)ˣ` and a power-of-two-sized (any size, really) register `Q`.
The algorithm prepares

  `Q^{-1/2} ∑_{j < Q} |j⟩ |u ^ j⟩`,

applies the quantum Fourier transform modulo `Q` to the first register and
measures.  The probability of observing `c` in the first register and `y` in the
second one is `Q^{-2} ‖∑_{j < Q, u ^ j = y} e^{2πι c j / Q}‖^2`, so the marginal
probability of observing `c` is the following quantity.
-/

/-- Probability that Shor's period-finding circuit, run with modulus `N`, base `u`
and register size `Q`, outputs the value `c`. -/

def DeterminesPeriod (Q M r c : ℕ) : Prop :=
  (∃ s : ℕ, Nat.Coprime s r ∧ |(c : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q)) ∧
    (∀ s' r' : ℕ, 0 < r' → r' ≤ M → Nat.Coprime s' r' →
      |(c : ℝ) / Q - (s' : ℝ) / r'| ≤ 1 / (2 * Q) → r' = r)

/-! ### `shorProb` is a probability distribution

The following two lemmas are not needed for the main theorem, but they certify
that `shorProb` really is the distribution of the measurement outcome: it is
nonnegative and its total mass over the `Q` possible outcomes is `1`. -/

