import Mathlib

/-!
# Admissible arithmetic-progression gap tuples

A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood prime
`k`-tuples conjecture) when, for every prime `p`, the reduction of `H` mod `p` omits at least
one residue class.  Equivalently, the local factor of the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` is nonzero at every prime.

This file characterises admissibility of the arithmetic progression tuples
`{0, d, 2d, …, (k-1)d}` and derives new admissible gap ranges for `90 ≤ k ≤ 98`.
-/

open scoped BigOperators

namespace Brockian

open Finset

/-- A finite set of integers is *admissible* if for every prime `p` it omits at least one
residue class modulo `p`. -/

theorem admissible_apTuple_iff (k : ℕ) (d : ℤ) :
    Admissible (apTuple k d) ↔ ∀ p : ℕ, p.Prime → p ≤ k → (p : ℤ) ∣ d := by
  constructor
  · intro hadm p hp hpk
    by_contra hdvd
    obtain ⟨r, hr⟩ := hadm p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hd : (d : ZMod p) ≠ 0 := by
      intro h0
      exact hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h0)
    set j : ℕ := (r * (d : ZMod p)⁻¹).val with hj
    have hjlt : j < p := ZMod.val_lt _
    have hmem : ((j : ℤ) * d) ∈ apTuple k d := by
      refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le hjlt hpk), rfl⟩
    have := hr _ hmem
    apply this
    push_cast
    rw [hj, ZMod.natCast_val, ZMod.cast_id]
    field_simp
  · intro hdvd p hp
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hpk : p ≤ k
    · refine ⟨1, ?_⟩
      intro h hh
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hh
      have hzero : (((j : ℤ) * d : ℤ) : ZMod p) = 0 := by
        have : ((p : ℤ)) ∣ ((j : ℤ) * d) := Dvd.dvd.mul_left (hdvd p hp hpk) _
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr this
      rw [hzero]
      exact zero_ne_one
    · exact exists_residue_notMem_of_card_lt hp
        (lt_of_le_of_lt (card_apTuple_le k d) (by omega))

/-- The primorial `n#`: the product of all primes `≤ n`. -/
