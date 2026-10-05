import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
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

/-- A finite set of integer offsets `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the reductions
of the elements of `H` modulo `p` miss at least one residue class.  This is exactly
the condition under which the singular series `𝔖(H)` is nonzero. -/

theorem exists_missed_residue_of_card_lt {H : Finset ℤ} {p : ℕ} [NeZero p]
    (h : H.card < p) : ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  classical
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hc r
    exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
  have hcard : (Finset.univ : Finset (ZMod p)).card ≤ H.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
  rw [Finset.card_univ, ZMod.card p] at hcard
  omega

/-- A pair `{0, g}` with `g` even is admissible. -/
