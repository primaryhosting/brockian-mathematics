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

theorem two_isPrimitiveRootMod_base_cases :
    ∀ p ∈ ({3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83} : Finset ℕ),
      p.Prime ∧ IsPrimitiveRootMod 2 p := by
  intro p hp
  fin_cases hp <;>
    exact ⟨by norm_num,
      isPrimitiveRootMod_two_of_bounded _ (by norm_num) (by decide) (by decide)⟩

/-- Reduction of the infinitude assertion in Artin's conjecture to an unboundedness
assertion. -/
