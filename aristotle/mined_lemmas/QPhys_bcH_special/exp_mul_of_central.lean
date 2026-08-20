import Mathlib

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

namespace QPhys

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- In a Banach algebra, `exp (x + y) = exp x * exp y` for commuting `x`, `y`. -/

theorem exp_mul_of_central (A B C : 𝔸) (hC : A * B - B * A = C)
    (hcentral : ∀ x : 𝔸, Commute C x) (t : ℝ) :
    exp (t • A) * B = (B + t • C) * exp (t • A) := by
  have h := exp_conj_of_central A B C hC hcentral t
  have := congrArg (fun z => z * exp (t • A)) h
  simp only [mul_assoc] at this
  rw [exp_neg_mul_exp] at this
  simpa [mul_assoc] using this

/-- **Baker–Campbell–Hausdorff, special case.**  If the commutator `[A, B] = AB - BA` is
central (commutes with every element of the algebra), then
`e^A e^B = e^{A + B + ½ [A, B]}`. -/
