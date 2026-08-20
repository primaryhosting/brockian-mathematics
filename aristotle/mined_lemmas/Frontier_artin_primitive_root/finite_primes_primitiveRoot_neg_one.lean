import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
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

set_option grind.warning false

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when its residue class generates the
multiplicative group of `ZMod p`, i.e. when it has multiplicative order `p - 1`. -/

lemma finite_primes_primitiveRoot_neg_one :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod (-1) p}.Finite := by
  refine Set.Finite.subset (Set.toFinite ({2, 3} : Set ℕ)) ?_
  rintro p ⟨hp, hpr⟩
  have hp3 : ¬ 3 < p := fun h => neg_one_not_primitiveRoot p hp h hpr
  have := hp.two_le
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases p
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Artin's primitive root conjecture: statement, necessity of its hypotheses, and a
base case.**

`Frontier.ArtinConjecture` states the (open) conjecture. This theorem records the
Lean-checked reduction accompanying it:

* both exclusions in the conjecture are necessary — a perfect square is never a primitive
  root modulo an odd prime, and `-1` is never a primitive root modulo a prime `p > 3`, so
  for those `a` the corresponding set of primes is *finite*, not infinite;
* primitive roots do exist modulo every prime;
* the base case `2` is a primitive root modulo `5`. -/
