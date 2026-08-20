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

/-- A finite set of integers is **admissible** (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) if, for every prime `p`, its reduction modulo `p` misses
at least one residue class. -/

theorem exists_missed_residue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro a _
    obtain ⟨h, hh, hha⟩ := hcon a
    exact Finset.mem_image.2 ⟨h, hh, hha⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at hle
  exact absurd (hle.trans Finset.card_image_le) (by omega)

/-- The `4`-tuple `(0, 2, 6, 8)` misses a residue class modulo `2`. -/
