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

lemma caseA_notExc (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) : ¬ IsExc (franklin S) := by
  have hmx := caseA_mx hA
  have hst := caseA_stair hne h0 hA hne2
  have hmn := caseA_mn hne hA
  have hlt : mn S < mx S - mn S + 1 := caseA_lt hne h0 hA hne2
  have h2 : mn S ≤ mx S := le_mx (mn_mem hne)
  rintro (h | ⟨c, hc, h | h⟩)
  · have hmem := caseA_mem_succ (S := S) hA
    rw [h] at hmem
    simp at hmem
  · have hle : c ≤ 2 * c - 1 := by omega
    have h1 : mn (franklin S) = c := by rw [h, mn_Icc hle]
    have h3 : stair (franklin S) = c := by rw [h, stair_Icc hle hc]; omega
    omega
  · have hle : c + 1 ≤ 2 * c := by omega
    have h3 : stair (franklin S) = c := by rw [h, stair_Icc hle (by omega)]; omega
    have h4 : mx (franklin S) = 2 * c := by rw [h, mx_Icc hle]
    omega

end CaseA

/-! ### Case B of the involution -/

section CaseB

variable {S : Finset ℕ}

