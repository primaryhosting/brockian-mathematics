import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
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

/-- The set of residue classes modulo `p` occupied by the tuple `H`. -/

lemma residues_subset_range (H : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    residues H p ⊆ Finset.range p := by
  intro r hr
  simp only [residues, Finset.mem_image] at hr
  obtain ⟨h, _, rfl⟩ := hr
  exact Finset.mem_range.mpr (Nat.mod_lt _ hp)

/-- Admissibility is equivalent to the local counts being strictly smaller than the modulus. -/
