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

lemma caseA_mn (hne : S.Nonempty) (hA : mn S ≤ stair S) : mn S < mn (franklin S) := by
  have hm : mn S ∈ S := mn_mem hne
  have h2 : mn S ≤ mx S := le_mx hm
  have hall : ∀ x ∈ franklin S, mn S < x := by
    intro x hx
    rw [caseA_franklin hA] at hx
    rcases Finset.mem_insert.1 hx with h | h
    · omega
    · have hxS : x ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
      have hxne : x ≠ mn S := (Finset.mem_erase.1 (Finset.mem_of_mem_erase h)).1
      have := mn_le hxS
      omega
  exact hall _ (mn_mem ⟨_, caseA_mem_succ (S := S) hA⟩)

