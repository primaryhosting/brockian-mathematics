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

lemma mn_le_mx_sub_stair {S : Finset ℕ} (hne : S.Nonempty) (h0 : 0 ∉ S) :
    mn S ≤ mx S - stair S + 1 := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have h3 : mx S - (stair S - 1) ∈ S := mem_of_lt_stair (by omega)
  have := mn_le h3
  omega

/-! ### The exceptional sets -/

