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

/-- `nu H p` is the number of distinct residue classes modulo `p` occupied by the
finite set of integers `H`.  These are the local densities appearing in the singular
series `𝔖(H) = ∏_p (1 - nu H p / p) / (1 - 1/p)^{|H|}` of the Hardy–Littlewood
prime tuples conjecture. -/

theorem nu_lt_of_missing_residue (H : Finset ℤ) (p : ℕ) [NeZero p] (r : ZMod p)
    (hr : ∀ h ∈ H, (h : ZMod p) ≠ r) : nu H p < p := by
  have hne : (H.image (fun h : ℤ => (h : ZMod p))) ≠ Finset.univ := by
    intro hcontra
    have hmem : r ∈ H.image (fun h : ℤ => (h : ZMod p)) := by
      rw [hcontra]; exact Finset.mem_univ r
    obtain ⟨h, hh, hhr⟩ := Finset.mem_image.1 hmem
    exact hr h hh hhr
  have := (Finset.card_lt_iff_ne_univ _).2 hne
  rwa [ZMod.card] at this

/-- If `nu H p < p` then some residue class mod `p` is missed by `H`. -/
