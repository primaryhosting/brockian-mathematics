/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- A finite set of integers `H` is *admissible* if for every prime `p` there is a residue
class mod `p` avoided by every element of `H`.  Equivalently, `H` does not cover all residues
modulo any prime; this is exactly the condition under which the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)/(1 - 1/p)^{|H|}` has no vanishing local factor. -/
def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The number of residues mod `p` occupied by `H`, i.e. the local factor datum `ν_H(p)`. -/
noncomputable def residueCount (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image (fun x : ℤ => (x : ZMod p))).card

/-- Admissibility is equivalent to the statement that every local factor
`1 - ν_H(p)/p` of the singular series is nonzero. -/
theorem isAdmissible_iff_residueCount_lt (H : Finset ℤ) :
    IsAdmissible H ↔ ∀ p : ℕ, p.Prime → residueCount H p < p := by
  constructor
  · intro hH p hp
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hsub : (H.image (fun x : ℤ => (x : ZMod p))) ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.mpr ?_
      intro hEq
      have hmem : r ∈ H.image (fun x : ℤ => (x : ZMod p)) := by simp [hEq]
      obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp hmem
      exact hr x hx hxr
    have hlt := Finset.card_lt_card hsub
    simpa [residueCount, ZMod.card p] using hlt
  · intro hH p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Fintype.card (ZMod p) := by
      simpa [residueCount, ZMod.card p] using hH p hp
    have hex : ∃ r : ZMod p, r ∉ H.image (fun x : ℤ => (x : ZMod p)) := by
      by_contra hc
      push_neg at hc
      have huniv : (H.image (fun x : ℤ => (x : ZMod p))) = Finset.univ :=
        Finset.eq_univ_of_forall hc
      simp [huniv] at hcard
    obtain ⟨r, hr⟩ := hex
    exact ⟨r, fun x hx hxr => hr (Finset.mem_image.mpr ⟨x, hx, hxr⟩)⟩

/-- Pigeonhole: a set with fewer than `p` elements always misses a residue mod `p`. -/
theorem exists_missing_residue_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (h : H.card < p) : ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Fintype.card (ZMod p) := by
    calc (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
      _ < p := h
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
  have hex : ∃ r : ZMod p, r ∉ H.image (fun x : ℤ => (x : ZMod p)) := by
    by_contra hc
    push_neg at hc
    have huniv : (H.image (fun x : ℤ => (x : ZMod p))) = Finset.univ :=
      Finset.eq_univ_of_forall hc
    simp [huniv] at hcard
  obtain ⟨r, hr⟩ := hex
  exact ⟨r, fun x hx hxr => hr (Finset.mem_image.mpr ⟨x, hx, hxr⟩)⟩

/-- **Singular Series Gaps 13501360.**
For every integer `n`, the triple `{n, n + 1350, n + 1360}` is admissible: it avoids at least
one residue class modulo every prime.  Thus the gap range pattern `(1350, 1360)` extends the
family of admissible gap configurations, and the associated singular series has no vanishing
local factor. -/
theorem SingularSeriesGaps13501360 (n : ℤ) :
    IsAdmissible {n, n + 1350, n + 1360} := by
  intro p hp
  -- The small primes `2` and `3` are treated by hand; for `p ≥ 5` pigeonhole suffices.
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨(n : ZMod 2) + 1, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh <;> rw [hh] <;> push_cast <;> intro hEq <;> revert hEq <;>
      generalize ((n : ZMod 2)) = a <;> revert a <;> decide
  rcases eq_or_ne p 3 with rfl | hp3
  · refine ⟨(n : ZMod 3) + 2, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh <;> rw [hh] <;> push_cast <;> intro hEq <;> revert hEq <;>
      generalize ((n : ZMod 3)) = a <;> revert a <;> decide
  · refine exists_missing_residue_of_card_lt hp ?_
    have hcard : ({n, n + 1350, n + 1360} : Finset ℤ).card ≤ 3 := by
      apply le_trans (Finset.card_insert_le _ _)
      have h2 := Finset.card_insert_le (n + 1350) ({n + 1360} : Finset ℤ)
      simp at h2 ⊢
    have h5 : 5 ≤ p := by
      by_contra hlt
      push_neg at hlt
      have h2 := hp.two_le
      interval_cases p <;> simp_all
    omega

end Brockian

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

