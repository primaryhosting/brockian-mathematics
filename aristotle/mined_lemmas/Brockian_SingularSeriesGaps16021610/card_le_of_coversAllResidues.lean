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

/-- `H` covers all residue classes modulo `p`. -/

theorem card_le_of_coversAllResidues {H : Finset ℕ} {p : ℕ}
    (h : CoversAllResidues H p) : p ≤ H.card := by
  have hsub : Finset.range p ⊆ H.image (fun x => x % p) := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := h r (Finset.mem_range.mp hr)
    exact Finset.mem_image.2 ⟨x, hx, hxr⟩
  calc p = (Finset.range p).card := (Finset.card_range p).symm
    _ ≤ (H.image (fun x => x % p)).card := Finset.card_le_card hsub
    _ ≤ H.card := Finset.card_image_le

/-- The concrete tuple inside the gap range `[1602, 1610]`. -/
