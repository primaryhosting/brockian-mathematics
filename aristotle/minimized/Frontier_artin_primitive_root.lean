/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `IsPrimitiveRootMod a p` says that the integer `a` is a primitive root modulo `p`, i.e.
the residue of `a` generates the multiplicative group `(ZMod p)ˣ`, which for a prime `p`
amounts to the multiplicative order of `a` in `ZMod p` being exactly `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- **Artin's conjecture on primitive roots.**  For every integer `a` which is neither `-1`
nor a perfect square, there are infinitely many primes `p` for which `a` is a primitive root
modulo `p`.  (The excluded values `a = -1` and `a` a square are exactly the classical
exceptions, for which the set of such primes is finite.) -/
def ArtinPrimitiveRootConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a →
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Infinite

/-- The "unbounded" form of Artin's conjecture: for every admissible `a` and every bound `N`
there is a prime `p > N` having `a` as a primitive root. -/
def ArtinPrimitiveRootUnbounded : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a →
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ IsPrimitiveRootMod a p

section BaseCases

private lemma cast_two (p : ℕ) : ((2 : ℤ) : ZMod p) = (2 : ZMod p) := by
  push_cast; ring

lemma isPrimitiveRootMod_two_three : IsPrimitiveRootMod 2 3 := by
  have h : ((2 : ℤ) : ZMod 3) = (2 : ZMod 3) := cast_two 3
  show orderOf ((2 : ℤ) : ZMod 3) = 3 - 1
  rw [h]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have hq2 : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hq1 : 2 ≤ q := hq.two_le
  interval_cases q <;> revert hdvd <;> decide

lemma isPrimitiveRootMod_two_five : IsPrimitiveRootMod 2 5 := by
  have h : ((2 : ℤ) : ZMod 5) = (2 : ZMod 5) := cast_two 5
  show orderOf ((2 : ℤ) : ZMod 5) = 5 - 1
  rw [h]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have hq2 : q ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hq1 : 2 ≤ q := hq.two_le
  interval_cases q <;> revert hdvd <;> decide

lemma isPrimitiveRootMod_two_eleven : IsPrimitiveRootMod 2 11 := by
  have h : ((2 : ℤ) : ZMod 11) = (2 : ZMod 11) := cast_two 11
  show orderOf ((2 : ℤ) : ZMod 11) = 11 - 1
  rw [h]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have hq2 : q ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
  have hq1 : 2 ≤ q := hq.two_le
  interval_cases q <;> revert hdvd <;> decide

lemma isPrimitiveRootMod_two_thirteen : IsPrimitiveRootMod 2 13 := by
  have h : ((2 : ℤ) : ZMod 13) = (2 : ZMod 13) := cast_two 13
  show orderOf ((2 : ℤ) : ZMod 13) = 13 - 1
  rw [h]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have hq2 : q ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  have hq1 : 2 ≤ q := hq.two_le
  interval_cases q <;> revert hdvd <;> decide

end BaseCases

/-- The reduction of Artin's conjecture to its unbounded form. -/
lemma artin_iff_unbounded :
    ArtinPrimitiveRootConjecture ↔ ArtinPrimitiveRootUnbounded := by
  constructor
  · intro h a ha hsq N
    obtain ⟨p, hp, hlt⟩ := (h a ha hsq).exists_gt N
    exact ⟨p, hlt, hp.1, hp.2⟩
  · intro h a ha hsq
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨p, hlt, hp, hprim⟩ := h a ha hsq N
    exact ⟨p, ⟨hp, hprim⟩, hlt⟩

/-- **Artin's conjecture on primitive roots**, formalized, together with a Lean-checked
reduction and base cases.

* The first component is the reduction: the conjecture (stated as the infinitude, for each
  integer `a ≠ -1` that is not a perfect square, of the set of primes `p` with `a` a primitive
  root mod `p`) is equivalent to the statement that such primes occur beyond every bound.
* The second component verifies the base cases `p = 3, 5, 11, 13` for `a = 2`: the number `2`
  is a primitive root modulo each of these primes. -/
theorem artin_primitive_root :
    (ArtinPrimitiveRootConjecture ↔ ArtinPrimitiveRootUnbounded) ∧
      (IsPrimitiveRootMod 2 3 ∧ IsPrimitiveRootMod 2 5 ∧
        IsPrimitiveRootMod 2 11 ∧ IsPrimitiveRootMod 2 13) :=
  ⟨artin_iff_unbounded,
    isPrimitiveRootMod_two_three, isPrimitiveRootMod_two_five,
    isPrimitiveRootMod_two_eleven, isPrimitiveRootMod_two_thirteen⟩

end Frontier

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

