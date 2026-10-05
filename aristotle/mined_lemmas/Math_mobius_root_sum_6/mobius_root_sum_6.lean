/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex

namespace Math

/-- The two primitive 6-th roots of unity, written explicitly. -/
private noncomputable def zA : ℂ := (1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2
private noncomputable def zB : ℂ := (1 - Complex.I * (Real.sqrt 3 : ℝ)) / 2


theorem mobius_root_sum_6 :
    ∑ ζ ∈ primitiveRoots 6 ℂ, ζ = (ArithmeticFunction.moebius 6 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (show Nat.Coprime 2 3 by decide),
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  rw [primitiveRoots_six, Finset.sum_pair zA_ne_zB, hmu]
  unfold zA zB
  push_cast
  ring

end Math

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

