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

lemma roundSample_inj {Q r : ℕ} (hr : 0 < r) (hQ : r < Q) :
    Function.Injective (roundSample Q r) := by
  intro a b hab
  obtain ⟨ha1, ha2⟩ := roundSample_bounds (Q := Q) (r := r) (s := a) hr
  obtain ⟨hb1, hb2⟩ := roundSample_bounds (Q := Q) (r := r) (s := b) hr
  rw [hab] at ha1 ha2
  have hQ' : (r : ℤ) < Q := by exact_mod_cast hQ
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  have k1 : (a : ℤ) ≤ b := by nlinarith
  have k2 : (b : ℤ) ≤ a := by nlinarith
  omega

/-! ### Main theorem -/

/-- **Shor's period finding works with high probability.**

Let `u` be a unit modulo `N` of multiplicative order `r`, and run the quantum
period-finding routine with a register of size `Q`, where `r ≤ M` and `M ^ 2 < Q`
(the usual choice is `M = N` and `Q` a power of two exceeding `N ^ 2`).  Then with
probability at least `φ(r) / (8 r)` the measured value `c` determines the period
`r` unambiguously: some fraction `s'/r'` in lowest terms with `r' ≤ M`
approximates `c / Q` to within `1 / (2 Q)`, and every such fraction has
denominator `r' = r`. -/
