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

theorem artinPrimes_neg_one_subset : artinPrimes (-1 : ℤ) ⊆ ({2, 3} : Set ℕ) := by
  intro p hp
  obtain ⟨hp, hprim⟩ := hp
  by_contra hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
  obtain ⟨hne2, hne3⟩ := hmem
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
  have hp5 : 5 ≤ p := by omega
  have hx0 : ((2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) (by omega)
  obtain ⟨n, hn⟩ := hprim ((2 : ℕ) : ZMod p) hx0
  have hcast : (((-1 : ℤ)) : ZMod p) = -1 := by push_cast; ring
  rw [hcast] at hn
  rcases neg_one_pow_eq_or (ZMod p) n with h | h <;> rw [h] at hn
  · have : ((1 : ℕ) : ZMod p) = 0 := by push_cast at hn ⊢; linear_combination -hn
    exact natCast_ne_zero_of_lt (by norm_num) (by omega) this
  · have : ((3 : ℕ) : ZMod p) = 0 := by push_cast at hn ⊢; linear_combination -hn
    exact natCast_ne_zero_of_lt (by norm_num) (by omega) this

/-- A bounded (hence decidable) criterion for being a primitive root. -/
