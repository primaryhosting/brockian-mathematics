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

def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  ∀ x : ZMod p, x ≠ 0 → ∃ n : ℕ, (a : ZMod p) ^ n = x

/-- The set of primes for which `a` is a primitive root. -/

theorem not_isPrimitiveRootMod_of_isSquare {a : ℤ} (ha : IsSquare a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, rfl⟩ := ha
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rwa [ZMod.ringChar_zmod_n]
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare hchar
  intro h
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (IsSquare.zero)
  obtain ⟨n, hn⟩ := h x hx0
  refine hx ⟨((b : ZMod p)) ^ n, ?_⟩
  rw [← hn]
  push_cast
  rw [mul_pow]

/-- `-1` is a primitive root only modulo `2` and `3`. -/
