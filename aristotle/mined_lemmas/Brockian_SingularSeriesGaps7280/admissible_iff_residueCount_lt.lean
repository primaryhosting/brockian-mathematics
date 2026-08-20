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

theorem admissible_iff_residueCount_lt {H : Finset ℕ} :
    Admissible H ↔ ∀ p : ℕ, p.Prime → residueCount H p < p := by
  constructor
  · rintro h p hp
    obtain ⟨r, hr, hmiss⟩ := h p hp
    exact residueCount_lt_of_miss hp.pos hr hmiss
  · intro h p hp
    have hlt := h p hp
    have hex : ∃ r ∈ Finset.range p, r ∉ H.image (· % p) := by
      by_contra hcon
      push_neg at hcon
      have hsub : Finset.range p ⊆ H.image (· % p) := fun r hr => hcon r hr
      have hle := Finset.card_le_card hsub
      rw [Finset.card_range] at hle
      exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)
    obtain ⟨r, hr, hrn⟩ := hex
    refine ⟨r, Finset.mem_range.1 hr, ?_⟩
    intro h' hh' hcon
    exact hrn (Finset.mem_image.2 ⟨h', hh', hcon⟩)

/-- For a prime `p`, positivity of the local factor of the singular series is exactly the
local admissibility condition at `p`. -/
