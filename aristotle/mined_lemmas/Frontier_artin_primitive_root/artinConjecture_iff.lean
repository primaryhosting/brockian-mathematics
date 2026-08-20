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

lemma artinConjecture_iff :
    ArtinConjecture ↔
      ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
        IsPrimitiveRootMod a p := by
  constructor
  · intro h a ha hsq N
    obtain ⟨p, hp, hlt⟩ := (h a ha hsq).exists_gt N
    exact ⟨p, hlt, hp.1, hp.2⟩
  · intro h a ha hsq
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨p, hlt, hp, hprim⟩ := h a ha hsq N
    exact ⟨p, ⟨hp, hprim⟩, hlt⟩

/-- If `a` is a primitive root mod the prime `p`, then `a` is invertible mod `p`. -/
