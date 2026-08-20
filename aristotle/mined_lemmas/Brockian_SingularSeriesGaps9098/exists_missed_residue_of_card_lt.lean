/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean 4 does not permit a module
-- docstring before `import`; the same header is repeated as a module docstring below.)


import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture: the singular series `𝔖(H)` is nonzero exactly for such `H`)
if for every prime `p` the reductions of the elements of `H` modulo `p` miss at least one
residue class. -/

theorem exists_missed_residue_of_card_lt (H : Finset ℤ) (p : ℕ) [Fact p.Prime]
    (hp : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  by_contra hcon
  push_neg at hcon
  -- if no residue is missed, the cast map from `H` is onto `ZMod p`
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hr⟩ := hcon r
    exact Finset.mem_image.2 ⟨h, hh, hr⟩
  have hcard : p ≤ H.card := by
    have h1 : (Finset.univ : Finset (ZMod p)).card ≤ (H.image fun h : ℤ => (h : ZMod p)).card :=
      Finset.card_le_card hsub
    have h2 : (H.image fun h : ℤ => (h : ZMod p)).card ≤ H.card := Finset.card_image_le
    have h3 : (Finset.univ : Finset (ZMod p)).card = p := by
      simp [ZMod.card]
    omega
  omega

/-- `0 ≠ 1` in `ZMod 2`. -/
