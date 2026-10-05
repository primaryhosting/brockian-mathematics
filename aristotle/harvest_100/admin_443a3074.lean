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

/-- A finite set of integer shifts `H` *avoids* the prime `p` when the shifts do not cover
all residue classes modulo `p`. -/
def AvoidsPrime (H : Finset ℤ) (p : ℕ) : Prop :=
  ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- A finite set of integer shifts is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when for every prime `p` it omits at least one residue class
modulo `p`; equivalently, its singular series is nonzero. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → AvoidsPrime H p

/-- A large prime is automatically avoided: a set of `k` shifts cannot cover all `p > k`
residue classes. -/
theorem avoidsPrime_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime) (hcard : H.card < p) :
    AvoidsPrime H p := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  simp only [AvoidsPrime, not_exists, not_forall, not_ne_iff] at hcon
  have hsurj : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hhr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
  have hle : (Finset.univ : Finset (ZMod p)).card ≤ H.card :=
    le_trans (Finset.card_le_card hsurj) (Finset.card_image_le)
  rw [Finset.card_univ, ZMod.card] at hle
  omega

/-- **Reduction to small primes.** To check admissibility of a `k`-element set of shifts it
suffices to check the primes `p ≤ k`.  (The proof splits on whether `p ≤ H.card`.) -/
theorem admissible_of_small_primes {H : Finset ℤ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → AvoidsPrime H p) : Admissible H := by
  intro p hp
  by_cases hle : p ≤ H.card
  · exact h p hp hle
  · exact avoidsPrime_of_card_lt hp (by omega)

/-- The candidate tuple: six shifts spanning the gap range `[0, 16]`. -/
def gapTuple16021610 : Finset ℤ := {0, 4, 6, 10, 12, 16}

theorem card_gapTuple16021610 : gapTuple16021610.card = 6 := by decide

/-- **Singular Series Gaps 16021610.**  The six shifts `{0, 4, 6, 10, 12, 16}` form an
admissible tuple of diameter `16`: every element lies in the gap range `[0, 16]`, the two
endpoints are attained, and for every prime `p` some residue class mod `p` is omitted, so the
associated singular series does not vanish.  For contrast, the naive tuple `{0, 2, 4}` is *not*
admissible, since it meets every residue class modulo `3`. -/
theorem SingularSeriesGaps16021610 :
    gapTuple16021610.card = 6 ∧
      (∀ h ∈ gapTuple16021610, 0 ≤ h ∧ h ≤ 16) ∧
      (0 : ℤ) ∈ gapTuple16021610 ∧ (16 : ℤ) ∈ gapTuple16021610 ∧
      Admissible gapTuple16021610 ∧
      ¬ Admissible ({0, 2, 4} : Finset ℤ) := by
  refine ⟨card_gapTuple16021610, by decide, by decide, by decide, ?_, ?_⟩
  · refine admissible_of_small_primes ?_
    rw [card_gapTuple16021610]
    intro p hp hple
    have h2 : 2 ≤ p := hp.two_le
    interval_cases p
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩
    · exact absurd hp (by decide)
    · exact ⟨3, by decide⟩
    · exact absurd hp (by decide)
  · intro hadm
    obtain ⟨r, hr⟩ := hadm 3 (by norm_num)
    revert hr
    revert r
    decide

end Brockian

