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

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of integer shifts `H` is *admissible* if for every prime `p` the
elements of `H` miss at least one residue class modulo `p`.  Equivalently, the
singular series `𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` attached to `H` is
nonzero, which is the necessary local condition in the Hardy–Littlewood prime
`k`-tuple conjecture. -/

theorem exists_missed_residue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : 0 < p)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨hp.ne'⟩
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hc r
    exact Finset.mem_image.2 ⟨x, hx, hxr⟩
  have h2 := Finset.card_le_card hsub
  simp only [Finset.card_univ, ZMod.card] at h2
  have h3 := Finset.card_image_le (s := H) (f := fun x : ℤ => (x : ZMod p))
  omega

/-- The classical prime octuplet pattern `{0, 2, 6, 8, 12, 18, 20, 26}` is admissible. -/
