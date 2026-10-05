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

lemma isoPlane_map_le (n : ℕ) [NeZero n] (k : ZMod n) (g : DihedralGroup n) :
    Submodule.map (ngonRep n g) (isoPlane n k) ≤ isoPlane n k := by
  rw [isoPlane, Submodule.map_span_le]
  rintro v hv
  rcases hv with rfl | rfl
  · cases g with
    | r i => rw [ngonRep_r_evec]; exact Submodule.smul_mem _ _ (evec_mem_isoPlane n k)
    | sr i => rw [ngonRep_sr_evec]; exact Submodule.smul_mem _ _ (evec_neg_mem_isoPlane n k)
  · cases g with
    | r i => rw [ngonRep_r_evec]; exact Submodule.smul_mem _ _ (evec_neg_mem_isoPlane n k)
    | sr i =>
      rw [ngonRep_sr_evec, neg_neg]
      exact Submodule.smul_mem _ _ (evec_mem_isoPlane n k)

/-- Each isotypic plane is a subrepresentation. -/
