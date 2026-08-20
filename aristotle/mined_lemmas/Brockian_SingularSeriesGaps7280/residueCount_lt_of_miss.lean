import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Admissible tuples and positivity of the singular series

An `H : Finset ℕ` (thought of as a set of *gaps* / offsets of a prime constellation
`n + h`, `h ∈ H`) is **admissible** when, for every prime `p`, the reductions of `H`
modulo `p` do not cover all residue classes.  This is exactly the condition under which
the local factors of the Hardy–Littlewood singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p) (1 - 1/p)^(-|H|)` are all positive.

This file develops the basic theory and a general criterion producing admissible sets:
a set of size at most `m`, all of whose elements are coprime to `m !`, is admissible.
-/

open scoped BigOperators Nat

namespace Brockian

/-- The number of residue classes mod `p` occupied by `H`, i.e. `ν_H(p)`. -/

theorem residueCount_lt_of_miss {H : Finset ℕ} {p r : ℕ} (hp : 0 < p) (hr : r < p)
    (hmiss : ∀ h ∈ H, h % p ≠ r) : residueCount H p < p := by
  have hsub : H.image (· % p) ⊆ (Finset.range p).erase r := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact Finset.mem_erase.2 ⟨hmiss a ha, Finset.mem_range.2 (Nat.mod_lt _ hp)⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_range.2 hr), Finset.card_range] at hle
  exact lt_of_le_of_lt hle (Nat.sub_lt hp one_pos)

/-- Admissibility is equivalent to `ν_H(p) < p` for all primes `p`. -/
