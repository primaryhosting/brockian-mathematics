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
def ThabitShape (k p m : ℕ) : Prop := m + (p + 2) = 2 ^ k * (p + 2)

/-- The delivered sigma criterion: `σ m = (2 ^ (k + 1) - 1) * (p + 1)`, written in
subtraction-free form over `ℕ`. -/
def SigmaCriterion (k p m : ℕ) : Prop := σ 1 m + (p + 1) = 2 ^ (k + 1) * (p + 1)

/-- **Thabit balance identity.**  If `m` has the Thabit shape `m = (2 ^ k - 1) * (p + 2)`
and satisfies the delivered sigma criterion `σ m = (2 ^ (k + 1) - 1) * (p + 1)`, then the
subtraction-free balance identity

`σ m + 2 ^ (k + 1) = 2 * m + (p + 3)`

holds. -/
theorem thabit_balance_identity {k p m : ℕ}
    (hshape : ThabitShape k p m) (hsigma : SigmaCriterion k p m) :
    σ 1 m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  unfold ThabitShape at hshape
  unfold SigmaCriterion at hsigma
  zify at hshape hsigma ⊢
  linear_combination hsigma - 2 * hshape

/-- Under the Thabit shape and the sigma criterion, `m` is deficient exactly when
`p + 3 < 2 ^ (k + 1)`. -/
theorem thabit_deficient_iff {k p m : ℕ}
    (hshape : ThabitShape k p m) (hsigma : SigmaCriterion k p m) :
    σ 1 m < 2 * m ↔ p + 3 < 2 ^ (k + 1) := by
  have h := thabit_balance_identity hshape hsigma
  omega

/-- Under the Thabit shape and the sigma criterion, `m` is perfect exactly when
`p + 3 = 2 ^ (k + 1)`. -/
theorem thabit_perfect_iff {k p m : ℕ}
    (hshape : ThabitShape k p m) (hsigma : SigmaCriterion k p m) :
    σ 1 m = 2 * m ↔ p + 3 = 2 ^ (k + 1) := by
  have h := thabit_balance_identity hshape hsigma
  omega

/-- Under the Thabit shape and the sigma criterion, `m` is abundant exactly when
`2 ^ (k + 1) < p + 3`. -/
theorem thabit_abundant_iff {k p m : ℕ}
    (hshape : ThabitShape k p m) (hsigma : SigmaCriterion k p m) :
    2 * m < σ 1 m ↔ 2 ^ (k + 1) < p + 3 := by
  have h := thabit_balance_identity hshape hsigma
  omega

/-- The hypotheses are satisfiable in a non-trivial way: `k = 4`, `p = 3`,
`m = (2 ^ 4 - 1) * 5 = 75`, and indeed `σ 75 = 124 = (2 ^ 5 - 1) * 4`. -/
example : ThabitShape 4 3 75 ∧ SigmaCriterion 4 3 75 := by
  refine ⟨?_, ?_⟩
  · show 75 + (3 + 2) = 2 ^ 4 * (3 + 2); decide
  · show σ 1 75 + (3 + 1) = 2 ^ (4 + 1) * (3 + 1); decide

/-- A deficient instance: `75` is deficient, matching `p + 3 = 6 < 32 = 2 ^ 5`. -/
example : σ 1 75 < 2 * 75 := by decide

end Dynamics
end BetrothedNumbers
end Brockian

