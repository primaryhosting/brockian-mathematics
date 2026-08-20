import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

lemma infinite_primes_with_primitive_root :
    {p : ℕ | p.Prime ∧ ∃ a : ℤ, IsPrimitiveRootMod a p}.Infinite := by
  apply Set.Infinite.mono (s := {p : ℕ | p.Prime}) _ Nat.infinite_setOf_prime
  intro p hp
  exact ⟨hp, exists_isPrimitiveRootMod hp⟩

