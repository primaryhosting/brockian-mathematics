import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` it fails to cover
all residue classes modulo `p`, i.e. some residue class mod `p` is missed by `H`.
This is the classical admissibility condition of the Hardy–Littlewood prime `k`-tuple
conjecture. -/

lemma admissible_pair_iff_even (d : ℕ) : Admissible {0, (d : ℤ)} ↔ Even d := by
  constructor
  · intro h
    by_contra hodd
    obtain ⟨r, hr⟩ := h 2 Nat.prime_two
    have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
    have hd : (((d : ℤ)) : ZMod 2) ≠ r := hr _ (by simp)
    rw [intCast_zmod_two_of_odd d hodd] at hd
    rw [Int.cast_zero] at h0
    have hr2 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
    rcases hr2 r with rfl | rfl
    · exact h0 rfl
    · exact hd rfl
  · intro hd p hp
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨1, ?_⟩
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · simp only [Int.cast_zero]; decide
      · rw [intCast_zmod_two_of_even d hd]; decide
    · obtain ⟨r, hr0, hrd⟩ := exists_residue_ne_pair hp hp2 0 ((d : ℤ) : ZMod p)
      refine ⟨r, ?_⟩
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · simpa using hr0
      · exact hrd

end Admissibility

section General

/-- The odd arithmetic factor of the singular series is always positive. -/
