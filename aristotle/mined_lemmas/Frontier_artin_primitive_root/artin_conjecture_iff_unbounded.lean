/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` has
multiplicative order exactly `p - 1`, i.e. it generates the group `(ZMod p)ˣ`. -/

theorem artin_conjecture_iff_unbounded :
    ArtinConjecture ↔
      ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p > N, p.Prime ∧ IsPrimitiveRootMod a p := by
  constructor
  · intro h a ha hsq N
    obtain ⟨p, hp, hpN⟩ := (h a ha hsq).exists_gt N
    exact ⟨p, hpN, hp⟩
  · intro h a ha hsq
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨p, hpN, hp⟩ := h a ha hsq N
    exact absurd (hN hp) (by omega)

/--
**Artin's conjecture on primitive roots**, together with the Lean-checked content
we can supply unconditionally:

1. the conjecture as a formal statement (`ArtinConjecture`), reduced to the equivalent
   statement that the primes with `a` as a primitive root are unbounded;
2. the excluded cases really are excluded — if `a` is a perfect square or `a = -1`,
   then `a` is a primitive root for only finitely many primes, so the hypotheses of
   the conjecture are necessary;
3. base cases: `2` is a primitive root modulo `3, 5, 11, 13, 19, 29`.
-/
