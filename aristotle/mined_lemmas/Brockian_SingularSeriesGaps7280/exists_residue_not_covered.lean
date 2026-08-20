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

/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian

/-- A finite set of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture / singular series) if for every prime `p` it fails to
cover all residue classes modulo `p`. -/

lemma exists_residue_not_covered {S : Finset ℤ} {p : ℕ} (hp : p.Prime) (h : S.card < p) :
    ∃ r : ZMod p, ∀ s ∈ S, (s : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ S.image (fun s : ℤ => (s : ZMod p)) := by
    intro r _
    obtain ⟨s, hs, hsr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨s, hs, hsr⟩
  have hcard : (Fintype.card (ZMod p)) ≤ S.card := by
    calc (Fintype.card (ZMod p)) = (Finset.univ : Finset (ZMod p)).card := by
            simp [Finset.card_univ]
      _ ≤ (S.image (fun s : ℤ => (s : ZMod p))).card := Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
  rw [ZMod.card p] at hcard
  omega

/-- An arithmetic progression of length `k` and common difference `d` is admissible
as soon as every prime `p ≤ k` divides `d`. -/
