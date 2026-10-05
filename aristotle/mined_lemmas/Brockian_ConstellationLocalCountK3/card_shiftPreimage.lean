import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The set of base points `x` of a translate of the shift `d` landing inside `S`,
i.e. `{x | x + d ∈ S}`. -/

theorem card_shiftPreimage (S : Finset G) (d : G) :
    (shiftPreimage S d).card = S.card := by
  unfold shiftPreimage
  apply Finset.card_bij (fun x _ => x + d)
  · intro a ha; simpa [shiftPreimage] using ha
  · intro a _ b _ h; exact add_right_cancel h
  · intro b hb; exact ⟨b - d, by simp [hb], by simp⟩

omit [AddCommGroup G] in
/-- A two-set intersection bound: `|A ∩ B| + |G| ≥ |A| + |B|`. -/
