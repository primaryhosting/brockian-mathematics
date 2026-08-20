/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
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

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` is *admissible* if for every prime `p` the residues of the
elements of `H` do not cover all of `ZMod p`, i.e. some residue class mod `p` is missed. -/
def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- If a set has fewer elements than `p`, its residues cannot cover all of `ZMod p`. -/
theorem exists_residue_not_hit {H : Finset ℤ} {p : ℕ} (hp : p.Prime) (hcard : H.card < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
  have h1 : (Finset.univ : Finset (ZMod p)).card ≤ (H.image (fun x : ℤ => (x : ZMod p))).card :=
    Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at h1
  have h2 := h1.trans (Finset.card_image_le)
  omega

/-- **Admissibility criterion for `4`-tuples.**  A set of four integers is an admissible
`4`-tuple as soon as it misses a residue class modulo `2` and a residue class modulo `3`;
all larger primes are automatically fine by counting. -/
theorem AdmissibilityKTupleK4 (H : Finset ℤ) (hcard : H.card = 4)
    (h2 : ∃ r : ZMod 2, ∀ h ∈ H, (h : ZMod 2) ≠ r)
    (h3 : ∃ r : ZMod 3, ∀ h ∈ H, (h : ZMod 3) ≠ r) :
    IsAdmissible H := by
  intro p hp
  rcases lt_or_ge p 5 with hlt | hge
  · interval_cases p
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact h2
    · exact h3
    · exact absurd hp (by norm_num)
  · exact exists_residue_not_hit hp (by omega)

/-- The classical prime quadruplet pattern `{0, 2, 6, 8}` is an admissible `4`-tuple. -/
theorem isAdmissible_zero_two_six_eight :
    IsAdmissible ({0, 2, 6, 8} : Finset ℤ) := by
  apply AdmissibilityKTupleK4
  · decide
  · refine ⟨1, ?_⟩
    intro h hh
    fin_cases hh <;> decide
  · refine ⟨1, ?_⟩
    intro h hh
    fin_cases hh <;> decide

end Brockian

