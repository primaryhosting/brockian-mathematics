/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open ArithmeticFunction

namespace Riemann.Mertens

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, where `μ` is the Möbius function. -/

theorem value_at_ten : mertens 10 = -1 := by
  have h4 : moebius 4 = 0 := moebius_eq_zero_of_not_squarefree not_squarefree_four
  have h8 : moebius 8 = 0 := moebius_eq_zero_of_not_squarefree not_squarefree_eight
  have h9 : moebius 9 = 0 := moebius_eq_zero_of_not_squarefree not_squarefree_nine
  rw [mertens, show Finset.Icc 1 10 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset ℕ) by decide]
  norm_num [Finset.sum_insert, Finset.mem_insert, h4, h8, h9, moebius_six, moebius_ten,
    moebius_apply_prime Nat.prime_two, moebius_apply_prime Nat.prime_three,
    moebius_apply_prime (show Nat.Prime 5 by norm_num),
    moebius_apply_prime (show Nat.Prime 7 by norm_num)]

end Riemann.Mertens

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

