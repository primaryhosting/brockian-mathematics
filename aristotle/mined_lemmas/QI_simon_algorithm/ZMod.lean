import RequestProject.SimonQuantum

/-!
# Recovering the hidden shift from the measured samples

Each run of the quantum subroutine returns a uniformly random `y ∈ s^⊥`.  After `m`
runs the classical post-processing solves the linear system `t ⬝ y_i = 0` and outputs the
unique nonzero solution, which succeeds exactly when the samples *determine* `s`.
We bound the number of sample sequences that fail to determine `s`.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- The samples `y : Fin m → BV n` determine the hidden shift `s`: the only vectors
orthogonal to all of them are `0` and `s`. -/

lemma ZMod.two_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by decide +kernel +revert

end Basic

end QI

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

import RequestProject.SimonOrtho

/-!
# The quantum step of Simon's algorithm

One query to the Simon oracle for `f`, sandwiched between Hadamard transforms on the
input register, produces the state

`2^(-n) * ∑ x, ∑ y, (-1)^(x·y) |y⟩ |f x⟩`,

so measuring the input register gives outcome `y` with probability
`∑ z (2^(-n) * ∑_{x : f x = z} (-1)^(x·y))^2`.  We prove that this distribution is exactly
the uniform distribution on the hyperplane `s^⊥`, where `s` is the hidden shift.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- The real character `b ↦ (-1)^b` of `ZMod 2`. -/
