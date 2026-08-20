/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A finite set of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture: its singular series is nonzero) when,
for every prime `p`, the elements of the set miss at least one residue class mod `p`. -/

theorem exists_missing_residue_of_card_lt (B : Finset ℕ) (p : ℕ) (h : B.card < p) :
    ∃ r : ℕ, r < p ∧ ∀ b ∈ B, b % p ≠ r := by
  by_contra hcon
  push_neg at hcon
  -- every residue in `Finset.range p` is attained by `B`
  have hsub : Finset.range p ⊆ B.image (· % p) := by
    intro r hr
    rw [Finset.mem_range] at hr
    obtain ⟨b, hb, hbr⟩ := hcon r hr
    exact Finset.mem_image.mpr ⟨b, hb, hbr⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  exact absurd (this.trans (Finset.card_image_le)) (by omega)

/-- Admissibility is invariant under translation. -/
