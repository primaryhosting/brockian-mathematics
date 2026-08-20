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
