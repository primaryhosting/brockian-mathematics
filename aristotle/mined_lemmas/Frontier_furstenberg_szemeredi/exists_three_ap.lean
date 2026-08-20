/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The counting function of a set of naturals: the number of elements of `A` below `n`. -/

theorem exists_three_ap {A : Set ℕ} (hA : 0 < upperDensity A) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  obtain ⟨ε, hε, hcount⟩ := exists_pos_frequently_count hA
  obtain ⟨n, hn, -, hcard⟩ := hcount (cornersTheoremBound (ε / 3))
  have hnot : ¬ ThreeAPFree (((Finset.range n).filter (· ∈ A) : Finset ℕ) : Set ℕ) :=
    roth_3ap_theorem_nat ε hε hn _ (Finset.filter_subset _ _) hcard
  rw [ThreeAPFree] at hnot
  push_neg at hnot
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := hnot
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb hc
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · refine ⟨a, b - a, by omega, ha.2, ?_, ?_⟩
    · have : a + (b - a) = b := by omega
      rw [this]; exact hb.2
    · have : a + 2 * (b - a) = c := by omega
      rw [this]; exact hc.2
  · refine ⟨c, b - c, by omega, hc.2, ?_, ?_⟩
    · have : c + (b - c) = b := by omega
      rw [this]; exact hb.2
    · have : c + 2 * (b - c) = a := by omega
      rw [this]; exact ha.2

/-- **Furstenberg–Szemerédi (base case)**: every set of natural numbers of positive upper
density contains arithmetic progressions of every length `k ≤ 3`, with positive common
difference.

The full theorem of Szemerédi (arbitrary `k`), which Furstenberg deduced from his multiple
recurrence theorem, is formalized as the statement `Frontier.SzemerediStatement`; it is reduced
to its finitary form in `Frontier.szemeredi_of_finitary`. The case `k ≤ 3` proved here rests on
Roth's theorem. -/
