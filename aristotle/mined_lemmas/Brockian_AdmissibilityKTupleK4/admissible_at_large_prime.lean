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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` is **admissible** (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when, for every prime `p`, the reductions of the elements of
`H` modulo `p` do not cover all residue classes mod `p`. -/

theorem admissible_at_large_prime (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  -- every residue class is attained, so `ZMod p` embeds into the image of `H`
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro a _
    obtain ⟨h, hh, rfl⟩ := hcon a
    exact Finset.mem_image_of_mem _ hh
  have h1 : (Finset.univ : Finset (ZMod p)).card ≤ H.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
  rw [Finset.card_univ, ZMod.card] at h1
  exact absurd h1 (not_le.mpr hcard)

/-- The classical admissible `4`-tuple `{0, 2, 6, 8}`: it has four elements, its diameter is
`8`, and it is admissible, i.e. for every prime `p` some residue class mod `p` is missed. -/
