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

set_option grind.warning false

namespace QC

variable {A : Type*}

/-- The CHSH operator associated to a tuple of observables
`A₀, A₁` (Alice) and `B₀, B₁` (Bob). -/

def chshOp [Mul A] [Add A] [Sub A] (A₀ A₁ B₀ B₁ : A) : A :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

section Ring

variable [Ring A] [StarRing A] {A₀ A₁ B₀ B₁ : A}

/-- The square of the CHSH operator equals `4` minus the product of the two commutators. -/
