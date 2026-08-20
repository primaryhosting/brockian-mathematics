/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- The *local count* of a constellation (admissible tuple) with shift set `H`
at the modulus `p`: the number of residue classes `a` mod `p` such that none of
the numbers `a + h`, `h ∈ H`, is divisible by `p`. -/

lemma localCount_eq_sub (p : ℕ) [NeZero p] (H : Finset ℤ) :
    localCount p H = p - (H.image (fun h : ℤ => -((h : ℤ) : ZMod p))).card := by
  have hcard : (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card
      + (Finset.univ.filter (fun a : ZMod p => ¬ ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card
      = (Finset.univ : Finset (ZMod p)).card :=
    Finset.card_filter_add_card_filter_not _
  rw [forbidden_eq_image] at hcard
  have hp : (Finset.univ : Finset (ZMod p)).card = p := by
    simp [ZMod.card p]
  rw [hp] at hcard
  simp only [localCount]
  omega

/-- Main statement: the local constellation count for `k = 3` tuples with shifts
`h₁, h₂, h₃`. -/
