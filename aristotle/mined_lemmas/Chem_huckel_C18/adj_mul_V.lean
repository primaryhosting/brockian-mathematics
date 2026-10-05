/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

theorem adj_mul_V : (SimpleGraph.cycleGraph 18).adjMatrix ℂ * V = V * Matrix.diagonal mu := by
  ext u k
  have hL : ((SimpleGraph.cycleGraph 18).adjMatrix ℂ * V) u k
      = Matrix.mulVec ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) (fun v => V v k) u := rfl
  rw [hL, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one u), Matrix.mul_diagonal]
  have h1 : V (u - 1) k = ch (u * k) * ch (-k) := by
    show ch ((u - 1) * k) = _
    rw [show (u - 1) * k = u * k + -k by rw [sub_mul, one_mul, sub_eq_add_neg], ch_add]
  have h2 : V (u + 1) k = ch (u * k) * ch k := by
    show ch ((u + 1) * k) = _
    rw [show (u + 1) * k = u * k + k by rw [add_mul, one_mul], ch_add]
  rw [h1, h2, show V u k = ch (u * k) from rfl, ← ch_add_ch_neg k]
  ring

/-- The Fourier matrix as a unit of the matrix algebra. -/
