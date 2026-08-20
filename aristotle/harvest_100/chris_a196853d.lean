/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when, for every prime `p`, it misses at least one
residue class modulo `p`.  Equivalently, the singular series attached to the tuple
is nonzero. -/
def AdmissibleSet (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r

/-- Admissibility is invariant under translation of the tuple. -/
theorem admissibleSet_map_addLeft {H : Finset ℤ} (hH : AdmissibleSet H) (a : ℤ) :
    AdmissibleSet (H.image (fun x => a + x)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨(a : ZMod p) + r, ?_⟩
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have := hr y hy
  push_cast
  simpa using this

/-- Only the primes `p ≤ #H` need to be checked for admissibility: for larger primes
the pigeonhole principle supplies a missing residue class. -/
theorem admissibleSet_of_small_primes {H : Finset ℤ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r) :
    AdmissibleSet H := by
  intro p hp
  by_cases hle : p ≤ H.card
  · exact h p hp hle
  · push_neg at hle
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Finset.univ.card (α := ZMod p) := by
      have h1 : (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
      have h2 : Finset.univ.card (α := ZMod p) = p := by
        simp [ZMod.card p]
      omega
    have : ∃ r : ZMod p, r ∉ H.image (fun x : ℤ => (x : ZMod p)) := by
      by_contra hcon
      push_neg at hcon
      have : Finset.univ ⊆ H.image (fun x : ℤ => (x : ZMod p)) := fun r _ => hcon r
      have := Finset.card_le_card this
      omega
    obtain ⟨r, hr⟩ := this
    refine ⟨r, ?_⟩
    intro x hx hcontra
    exact hr (Finset.mem_image.mpr ⟨x, hx, hcontra⟩)

/-- The `9`-tuple of shifts studied here: an admissible pattern of `9` integers of
diameter `30`. -/
def gapPattern9098 : Finset ℤ := {0, 2, 6, 8, 12, 18, 20, 26, 30}

theorem gapPattern9098_card : gapPattern9098.card = 9 := by decide

theorem gapPattern9098_admissible : AdmissibleSet gapPattern9098 := by
  apply admissibleSet_of_small_primes
  intro p hp hle
  rw [gapPattern9098_card] at hle
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨4, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨3, by decide⟩
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)

/-- **Singular Series Gaps 9098.**
The `9`-element pattern `{0, 2, 6, 8, 12, 18, 20, 26, 30}` of diameter `30` is admissible,
and so is every one of its integer translates; consequently the whole family of gap
ranges `{a, a+2, a+6, a+8, a+12, a+18, a+20, a+26, a+30}` consists of admissible
`9`-tuples, each of which has nonvanishing singular series. -/
theorem SingularSeriesGaps9098 :
    gapPattern9098.card = 9 ∧
    (∀ x ∈ gapPattern9098, (0 : ℤ) ≤ x ∧ x ≤ 30) ∧
    AdmissibleSet gapPattern9098 ∧
    ∀ a : ℤ, AdmissibleSet (gapPattern9098.image (fun x => a + x)) := by
  refine ⟨gapPattern9098_card, by decide, gapPattern9098_admissible, ?_⟩
  intro a
  exact admissibleSet_map_addLeft gapPattern9098_admissible a

end Brockian

