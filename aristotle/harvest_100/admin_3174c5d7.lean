/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file states **Artin's conjecture on primitive roots** and proves, in Lean,

* a decidable *reduction*: `a` is a primitive root mod `p` iff `a ^ (p-1) = 1` and
  `a ^ ((p-1)/q) ≠ 1` for every prime `q ∣ p - 1`;
* a *reduction* of the infinitude statement in the conjecture to an unboundedness
  statement;
* *base cases*: `2` is a primitive root modulo each of
  `3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83`.

The conjecture itself (`Frontier.ArtinConjecture`) is stated as a `Prop`; it is open.
-/

namespace Frontier

/-- `a` is a primitive root modulo `p`: the residue of `a` generates the
multiplicative group `(ZMod p)ˣ`, i.e. it has order `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- **Artin's conjecture on primitive roots.** For every integer `a` which is neither
`-1` nor a perfect square (this excludes `0` and `1` as well), there are infinitely many
primes `p` for which `a` is a primitive root modulo `p`. -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a →
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Infinite

/-- Order criterion: for a prime `p`, `a` is a primitive root mod `p` exactly when
`a ^ (p-1) = 1` and `a ^ ((p-1)/q) ≠ 1` for every prime `q` dividing `p - 1`. -/
theorem isPrimitiveRootMod_iff (a : ℤ) (p : ℕ) (hp : p.Prime) :
    IsPrimitiveRootMod a p ↔
      ((a : ZMod p) ^ (p - 1) = 1 ∧
        ∀ q : ℕ, q.Prime → q ∣ (p - 1) → (a : ZMod p) ^ ((p - 1) / q) ≠ 1) := by
  have hp1 : 0 < p - 1 := by
    have := hp.two_le; omega
  constructor
  · intro h
    refine ⟨by rw [← h]; exact pow_orderOf_eq_one _, ?_⟩
    intro q hq hdvd
    refine pow_ne_one_of_lt_orderOf ?_ ?_
    · have : 0 < (p - 1) / q := Nat.div_pos (Nat.le_of_dvd hp1 hdvd) hq.pos
      omega
    · rw [h]
      exact Nat.div_lt_self hp1 hq.one_lt
  · rintro ⟨h1, h2⟩
    exact orderOf_eq_of_pow_and_pow_div_prime hp1 h1 h2

/-- Practical form of the criterion for `a = 2`, with the divisor search bounded by `p`
so that it can be discharged by decision procedures. -/
theorem isPrimitiveRootMod_two_of_bounded (p : ℕ) (hp : p.Prime)
    (h1 : (2 : ZMod p) ^ (p - 1) = 1)
    (h2 : ∀ q < p, q.Prime → q ∣ (p - 1) → (2 : ZMod p) ^ ((p - 1) / q) ≠ 1) :
    IsPrimitiveRootMod 2 p := by
  have hcast : (((2 : ℤ) : ZMod p)) = (2 : ZMod p) := by push_cast; ring
  rw [isPrimitiveRootMod_iff _ _ hp, hcast]
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  refine ⟨h1, fun q hq hdvd => ?_⟩
  exact h2 q (lt_of_le_of_lt (Nat.le_of_dvd hp1 hdvd) (by omega)) hq hdvd

set_option maxRecDepth 100000 in
/-- Base cases: `2` is a primitive root modulo each prime in the list
`3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83`. -/
theorem two_isPrimitiveRootMod_base_cases :
    ∀ p ∈ ({3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83} : Finset ℕ),
      p.Prime ∧ IsPrimitiveRootMod 2 p := by
  intro p hp
  fin_cases hp <;>
    exact ⟨by norm_num,
      isPrimitiveRootMod_two_of_bounded _ (by norm_num) (by decide) (by decide)⟩

/-- Reduction of the infinitude assertion in Artin's conjecture to an unboundedness
assertion. -/
theorem artinConjecture_iff_unbounded :
    ArtinConjecture ↔
      ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a →
        ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ IsPrimitiveRootMod a p := by
  constructor
  · intro h a ha hsq N
    obtain ⟨p, hp, hlt⟩ := (h a ha hsq).exists_gt N
    exact ⟨p, hlt, hp.1, hp.2⟩
  · intro h a ha hsq
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨p, hlt, hp, hroot⟩ := h a ha hsq N
    exact ⟨p, ⟨hp, hroot⟩, hlt⟩

/-- **Artin's conjecture on primitive roots**, together with the Lean-checked reductions
and base cases proved above:

1. the order criterion characterising primitive roots mod `p` by a finite computation;
2. the equivalence of the conjecture with the corresponding unboundedness statement;
3. the verified base cases for `a = 2` and the primes below `100` for which `2` is a
   primitive root, up to `83`. -/
theorem artin_primitive_root :
    (∀ (a : ℤ) (p : ℕ), p.Prime →
        (IsPrimitiveRootMod a p ↔
          ((a : ZMod p) ^ (p - 1) = 1 ∧
            ∀ q : ℕ, q.Prime → q ∣ (p - 1) → (a : ZMod p) ^ ((p - 1) / q) ≠ 1)))
      ∧ (ArtinConjecture ↔
          ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a →
            ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ IsPrimitiveRootMod a p)
      ∧ (∀ p ∈ ({3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83} : Finset ℕ),
          p.Prime ∧ IsPrimitiveRootMod 2 p) :=
  ⟨isPrimitiveRootMod_iff, artinConjecture_iff_unbounded, two_isPrimitiveRootMod_base_cases⟩

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

