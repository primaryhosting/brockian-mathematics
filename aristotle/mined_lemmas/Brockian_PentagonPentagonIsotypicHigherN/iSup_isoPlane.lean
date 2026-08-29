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

theorem iSup_isoPlane (n : ℕ) [NeZero n] : (⨆ k : ZMod n, isoPlane n k) = ⊤ := by
  rw [eq_top_iff, ← span_range_evec n, Submodule.span_le]
  rintro v ⟨k, rfl⟩
  exact Submodule.mem_iSup_of_mem k (evec_mem_isoPlane n k)

/-- Isotypic planes with `k ≠ -k` are genuinely two-dimensional. -/
