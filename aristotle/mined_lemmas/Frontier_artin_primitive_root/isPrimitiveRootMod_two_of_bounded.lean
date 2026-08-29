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
