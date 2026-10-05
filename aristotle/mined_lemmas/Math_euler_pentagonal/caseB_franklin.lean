import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-! ## Distinct partitions as finsets of positive integers -/

/-- The finset of all "partitions of `n` into distinct parts", encoded as finsets of
positive integers whose sum is `n`. -/

lemma caseB_franklin {S : Finset ℕ} (hB : stair S < mn S) :
    franklin S = insert (stair S) (insert (mx S - stair S) (S.erase (mx S))) := by
  rw [franklin, if_neg (by omega)]

/-! ### Case A of the involution -/

section CaseA

variable {S : Finset ℕ}

