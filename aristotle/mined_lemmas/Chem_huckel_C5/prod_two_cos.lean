/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`):
vertices are indexed by `Fin 5` with cyclic successor `i ↦ i + 1`, and `i, j` are adjacent
iff one is the cyclic successor of the other. -/

lemma prod_two_cos :
    (∏ k ∈ Finset.range 5, (X - C (2 * Real.cos (2 * π * k / 5))))
      = X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_one]
  push_cast
  rw [two_cos_zero, two_cos_one, two_cos_two, two_cos_three, two_cos_four]
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hab : (√5 - 1) / 2 + -(1 + √5) / 2 = -1 := by ring
  have hab2 : ((√5 - 1) / 2) * (-(1 + √5) / 2) = -1 := by nlinarith [h5]
  have e1 : ((X : ℝ[X]) - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2)) = X ^ 2 + X - 1 := by
    have h : ((X : ℝ[X]) - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))
        = X ^ 2 - C ((√5 - 1) / 2 + -(1 + √5) / 2) * X + C (((√5 - 1) / 2) * (-(1 + √5) / 2)) := by
      simp only [map_add, map_mul]; ring
    rw [h, hab, hab2]
    simp
    ring
  have h : ((((X - C (2 : ℝ)) * (X - C ((√5 - 1) / 2))) * (X - C (-(1 + √5) / 2)))
        * (X - C (-(1 + √5) / 2))) * (X - C ((√5 - 1) / 2))
      = (X - C (2 : ℝ)) * (((X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))) ^ 2) := by ring
  rw [h, e1]
  simp only [map_ofNat]
  ring

/-- **Hückel theory for cyclopentadienyl (C₅).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₅` factors
completely as `∏_{k=0}^{4} (X - 2cos(2πk/5))`; that is, the adjacency eigenvalues of `C₅`
are exactly `2cos(2πk/5)` for `k = 0, 1, 2, 3, 4`, counted with multiplicity. -/
