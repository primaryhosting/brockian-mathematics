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

lemma caseA_top_mem_erase (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) : mx S - mn S + 1 ∈ S.erase (mn S) :=
  Finset.mem_erase.2 ⟨fun h => hne2 h.symm, caseA_mem_top hne h0 hA⟩

