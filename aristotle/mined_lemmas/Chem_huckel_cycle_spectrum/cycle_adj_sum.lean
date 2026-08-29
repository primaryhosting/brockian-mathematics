/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Polynomial Matrix SimpleGraph Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma cycle_adj_sum (w : Fin (m + 3) → ℂ) (i : Fin (m + 3)) :
    ∑ j, ((cycleGraph (m + 3)).adjMatrix ℂ) i j * w j = w (i - 1) + w (i + 1) := by
  have hne : (i - 1) ≠ (i + 1) := by
    intro h
    have h2 : ((i - 1 : Fin (m + 3)) : ℕ) = ((i + 1 : Fin (m + 3)) : ℕ) := by rw [h]
    have hs : (i - 1 : Fin (m + 3)) + 1 + 1 = i + 1 + 1 := by rw [h]
    have : (i : Fin (m + 3)) + 1 + 1 = i := by
      rw [← hs]; ring_nf; rw [sub_add_cancel]
    have hval : ((i + 1 + 1 : Fin (m + 3)) : ℕ) = (i : ℕ) := by rw [this]
    simp only [Fin.val_add, Fin.val_one] at hval
    omega
  have hsum : ∑ j, ((cycleGraph (m + 3)).adjMatrix ℂ) i j * w j
      = ∑ j ∈ (cycleGraph (m + 3)).neighborFinset i, w j := by
    rw [Finset.sum_congr rfl (g := fun j => if (cycleGraph (m + 3)).Adj i j then w j else 0)
      (by intro j _; by_cases h : (cycleGraph (m + 3)).Adj i j <;> simp [h])]
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [SimpleGraph.mem_neighborFinset]
  rw [hsum]
  have : (cycleGraph (m + 1 + 2)).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset
  rw [show m + 3 = m + 1 + 2 from rfl] at *
  rw [this, Finset.sum_pair hne]

