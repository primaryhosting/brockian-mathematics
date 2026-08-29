/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian

open DihedralGroup

noncomputable section

/-! ## The root of unity -/

/-- A primitive `n`-th root of unity in `ℂ`. -/

theorem isoPlane_invariant (n : ℕ) [NeZero n] (k : ZMod n) (g : DihedralGroup n) :
    Submodule.map (ngonRep n g) (isoPlane n k) = isoPlane n k := by
  refine le_antisymm (isoPlane_map_le n k g) ?_
  intro v hv
  refine ⟨ngonRep n g⁻¹ v, isoPlane_map_le n k g⁻¹ ⟨v, hv, rfl⟩, ?_⟩
  have : (ngonRep n g) ((ngonRep n g⁻¹) v) = (ngonRep n (g * g⁻¹)) v := by
    rw [map_mul]; rfl
  rw [this, mul_inv_cancel, map_one]
  rfl

/-! ## Linear independence and the isotypic decomposition -/

