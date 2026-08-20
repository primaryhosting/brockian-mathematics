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
