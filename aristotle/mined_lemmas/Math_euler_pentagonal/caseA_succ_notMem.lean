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

lemma caseA_succ_notMem :
    mx S + 1 ∉ (S.erase (mn S)).erase (mx S - mn S + 1) := by
  intro h
  have hS : mx S + 1 ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
  have := le_mx hS
  omega

