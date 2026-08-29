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

lemma one_le_mn (hne : S.Nonempty) (h0 : 0 ∉ S) : 1 ≤ mn S :=
  Nat.one_le_iff_ne_zero.2 (fun h => h0 (h ▸ mn_mem hne))

