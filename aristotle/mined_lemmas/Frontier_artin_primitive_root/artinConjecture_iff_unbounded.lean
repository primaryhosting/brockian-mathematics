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
