/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` (a "tuple") is *admissible* when, for every prime `p`,
the reductions of the elements of `H` modulo `p` do not cover all residue classes mod `p`.
This is the classical Hardy–Littlewood admissibility condition for prime `k`-tuples. -/
def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- If `H` has fewer than `p` elements, then its reductions mod `p` miss some residue class. -/
lemma exists_missing_residue_of_card_lt (H : Finset ℤ) (p : ℕ) [NeZero p]
    (hp : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hr⟩ := hcon r
    exact Finset.mem_image.2 ⟨h, hh, hr⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at h1
  have h2 := h1.trans Finset.card_image_le
  omega

/-- **Admissibility criterion for 4-tuples.**
A set `H` of four integers is admissible (in the Hardy–Littlewood sense: for every prime `p`
its reductions mod `p` omit at least one residue class) if and only if this holds for the
two primes `p = 2` and `p = 3`.  All primes `p ≥ 5` are automatic, since four residues cannot
cover `p ≥ 5` classes. -/
theorem AdmissibilityKTupleK4 (H : Finset ℤ) (hH : H.card = 4) :
    IsAdmissible H ↔
      ((∃ r : ZMod 2, ∀ h ∈ H, (h : ZMod 2) ≠ r) ∧
       (∃ r : ZMod 3, ∀ h ∈ H, (h : ZMod 3) ≠ r)) := by
  constructor
  · intro h
    exact ⟨h 2 Nat.prime_two, h 3 Nat.prime_three⟩
  · rintro ⟨h2, h3⟩ p hp
    by_cases hlt : p < 5
    · interval_cases p
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
      · exact h2
      · exact h3
      · exact absurd hp (by decide)
    · have : NeZero p := ⟨hp.ne_zero⟩
      exact exists_missing_residue_of_card_lt H p (by omega)

/-- The classical admissible 4-tuple `(0, 2, 6, 8)`: it is indeed admissible. -/
theorem isAdmissible_zero_two_six_eight : IsAdmissible ({0, 2, 6, 8} : Finset ℤ) := by
  rw [AdmissibilityKTupleK4 _ (by decide)]
  exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

end Brockian

