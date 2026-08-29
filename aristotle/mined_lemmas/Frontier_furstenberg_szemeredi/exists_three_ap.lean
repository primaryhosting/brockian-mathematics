import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The number of elements of `A` below `n`. -/

lemma exists_three_ap {A : Set ℕ} (hA : HasPositiveUpperDensity A) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  obtain ⟨δ, hδ, h⟩ := hA
  obtain ⟨n, hn, hcard⟩ := h (cornersTheoremBound (δ / 3))
  have hnot := roth_3ap_theorem_nat δ hδ hn ((Finset.range n).filter (fun x => x ∈ A))
    (Finset.filter_subset _ _) (by simpa [countIn] using hcard)
  rw [ThreeAPFree] at hnot
  push_neg at hnot
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := hnot
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb hc
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · refine ⟨a, b - a, by omega, ha.2, ?_, ?_⟩
    · have e : a + (b - a) = b := by omega
      rw [e]; exact hb.2
    · have e : a + 2 * (b - a) = c := by omega
      rw [e]; exact hc.2
  · refine ⟨c, b - c, by omega, hc.2, ?_, ?_⟩
    · have e : c + (b - c) = b := by omega
      rw [e]; exact hb.2
    · have e : c + 2 * (b - c) = a := by omega
      rw [e]; exact ha.2

/-- **Furstenberg–Szemerédi (case `k ≤ 3`).**
Every set of natural numbers of positive upper density contains an arithmetic progression of
length `k` for every `k ≤ 3`.  The cases `k ≤ 2` are elementary; the case `k = 3` is Roth's
theorem. -/
