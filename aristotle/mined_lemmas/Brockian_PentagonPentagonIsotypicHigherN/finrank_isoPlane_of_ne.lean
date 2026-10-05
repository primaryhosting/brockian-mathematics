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

theorem finrank_isoPlane_of_ne (n : ℕ) [NeZero n] (k : ZMod n) (hk : k ≠ -k) :
    Module.finrank ℂ (isoPlane n k) = 2 := by
  have hne : evec n k ≠ evec n (-k) := fun h => hk (evec_injective n h)
  have hli : LinearIndepOn ℂ id ({evec n k, evec n (-k)} : Set (ZMod n → ℂ)) := by
    refine ((evec_linearIndependent n).linearIndepOn_id).mono ?_
    rintro v hv
    rcases hv with rfl | rfl
    · exact ⟨k, rfl⟩
    · exact ⟨-k, rfl⟩
  have := finrank_span_set_eq_card (R := ℂ) hli
  rw [isoPlane, this]
  rw [Set.toFinset_insert, Set.toFinset_singleton]
  rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- Isotypic planes with `k = -k` (the trivial and, for even `n`, the sign line) are lines. -/
