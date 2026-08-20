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

lemma exists_residue_notMem_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  have huniv : (H.image (fun h : ℤ => (h : ZMod p))) = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr ?_
    intro r
    obtain ⟨h, hh, hhr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
  have h1 : (Finset.univ : Finset (ZMod p)).card ≤ H.card := by
    rw [← huniv]; exact Finset.card_image_le
  rw [Finset.card_univ, ZMod.card] at h1
  omega

/-- **Characterisation of admissible AP gap tuples.**  The progression
`{0, d, 2d, …, (k-1)d}` is admissible if and only if every prime `p ≤ k` divides `d`. -/
