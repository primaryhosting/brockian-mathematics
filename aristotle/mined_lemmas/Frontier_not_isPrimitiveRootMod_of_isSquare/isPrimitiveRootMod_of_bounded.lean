/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` if every nonzero residue class mod `p`
is a power of `a`, i.e. `a` generates the multiplicative group `(ZMod p)ˣ`. -/

theorem isPrimitiveRootMod_of_bounded {a : ℤ} {p : ℕ}
    (h : ∀ x : ZMod p, x ≠ 0 → ∃ n ∈ Finset.range p, (a : ZMod p) ^ n = x) :
    IsPrimitiveRootMod a p := by
  intro x hx
  obtain ⟨n, -, hn⟩ := h x hx
  exact ⟨n, hn⟩

/-- `2` is a primitive root modulo `5`. -/
