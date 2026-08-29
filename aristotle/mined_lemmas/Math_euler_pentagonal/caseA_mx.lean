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

lemma caseA_mx (hA : mn S ≤ stair S) : mx (franklin S) = mx S + 1 := by
  have hmem := caseA_mem_succ (S := S) hA
  refine le_antisymm ?_ (le_mx hmem)
  have hall : ∀ x ∈ franklin S, x ≤ mx S + 1 := by
    intro x hx
    rw [caseA_franklin hA] at hx
    rcases Finset.mem_insert.1 hx with h | h
    · omega
    · have := le_mx (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
      omega
  exact hall _ (mx_mem ⟨_, hmem⟩)

