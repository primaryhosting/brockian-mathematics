/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

namespace Brockian

/-- A finite set of integers `H` (a *pattern*, or *gap tuple*) is **admissible** when for every
prime `p` the reductions of the elements of `H` modulo `p` miss at least one residue class.
This is exactly the condition under which every local factor `1 - ν_p(H)/p` of the
Hardy–Littlewood singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` is nonzero. -/

theorem exists_missed_residue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hhr⟩ := hcon r
    exact Finset.mem_image.2 ⟨h, hh, hhr⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
  rw [Finset.card_univ, ZMod.card] at h1
  omega

/-- The local condition at `p = 2` for a pair `{0, g}`: the pair misses a residue class
modulo `2` exactly when the gap `g` is even. -/
