import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ArithmeticFunction.sigma

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

namespace Brockian
namespace BetrothedNumbers
namespace Dynamics

/-- The Thabit-type shape of the modulus: `m = (2 ^ k - 1) * (p + 2)`, written in
subtraction-free form so that it makes sense verbatim over `ℕ`. -/

theorem thabit_balance_identity {k p m : ℕ}
    (hshape : ThabitShape k p m) (hsigma : SigmaCriterion k p m) :
    σ 1 m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  unfold ThabitShape at hshape
  unfold SigmaCriterion at hsigma
  zify at hshape hsigma ⊢
  linear_combination hsigma - 2 * hshape

/-- Under the Thabit shape and the sigma criterion, `m` is deficient exactly when
`p + 3 < 2 ^ (k + 1)`. -/
