/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) if for every prime `p` the elements of `H` do not cover all
residue classes modulo `p`.  Equivalently, the local factor of the singular series
`𝔖(H) = ∏_p (1 - 1/p)^{-|H|} (1 - ν_p(H)/p)` is nonzero at every prime. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- Key intermediate lemma: admissibility only has to be checked at the primes `p ≤ |H|`.
Indeed, a set of `|H|` residues can never cover the `p > |H|` classes modulo `p`. -/
theorem admissible_of_small_primes (H : Finset ℤ)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) :
    Admissible H := by
  intro p hp
  rcases le_or_gt p H.card with hle | hlt
  · exact hsmall p hp hle
  · by_contra hcon
    push_neg at hcon
    haveI : Fact p.Prime := ⟨hp⟩
    have hsurj : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
      intro r _
      obtain ⟨h, hh, hr⟩ := hcon r
      exact Finset.mem_image.2 ⟨h, hh, hr⟩
    have h1 := Finset.card_le_card hsurj
    simp [ZMod.card] at h1
    have h2 := H.card_image_le (f := fun h : ℤ => (h : ZMod p))
    omega

/-- Admissibility is invariant under translation of the tuple. -/
theorem admissible_translate {H : Finset ℤ} (hH : Admissible H) (n : ℤ) :
    Admissible (H.image (fun h => h + n)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨r + (n : ZMod p), ?_⟩
  rintro x hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
  simpa using fun hcon => hr h hh (by exact_mod_cast hcon)

/-- The gap pattern `0, 2, 6, 8, 12, 18, 20, 26`: an `8`-tuple of diameter `26`. -/
def gapTuple : Finset ℤ := {0, 2, 6, 8, 12, 18, 20, 26}

theorem gapTuple_card : gapTuple.card = 8 := by decide

/-- Every element of the pattern lies in the gap range `[0, 26]`, and the endpoints
of that range are attained, so the pattern has diameter exactly `26`. -/
theorem gapTuple_range :
    (0 : ℤ) ∈ gapTuple ∧ (26 : ℤ) ∈ gapTuple ∧ ∀ h ∈ gapTuple, 0 ≤ h ∧ h ≤ 26 := by
  refine ⟨by decide, by decide, ?_⟩
  decide

theorem gapTuple_admissible : Admissible gapTuple := by
  apply admissible_of_small_primes
  intro p hp hple
  rw [gapTuple_card] at hple
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

/-- **Singular Series Gaps 16021610.**
The pattern `H = {0, 2, 6, 8, 12, 18, 20, 26}` is an admissible `8`-tuple lying in the
gap range `[0, 26]` (with both endpoints attained), and every translate `H + n` of it is
again admissible.  Hence for each prime `p` the local factor `1 - ν_p(H)/p` of the
singular series `𝔖(H)` is nonzero, so the Hardy–Littlewood conjecture predicts infinitely
many translates of this range consisting of `8` primes. -/
theorem SingularSeriesGaps16021610 :
    gapTuple.card = 8 ∧
    ((0 : ℤ) ∈ gapTuple ∧ (26 : ℤ) ∈ gapTuple ∧ ∀ h ∈ gapTuple, 0 ≤ h ∧ h ≤ 26) ∧
    Admissible gapTuple ∧
    ∀ n : ℤ, Admissible (gapTuple.image (fun h => h + n)) :=
  ⟨gapTuple_card, gapTuple_range, gapTuple_admissible,
    fun n => admissible_translate gapTuple_admissible n⟩

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

