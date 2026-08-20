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

theorem neg_one_primes_subset :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod (-1) p} ⊆ {2, 3} := by
  intro p hp
  by_contra hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  have h2 := hp.1.two_le
  exact not_isPrimitiveRootMod_neg_one hp.1 (by omega) hp.2

/-- Both exceptional cases of Artin's conjecture give a *finite* set of primes,
so the hypotheses `a ≠ -1` and `¬ IsSquare a` are necessary. -/
