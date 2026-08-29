import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
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

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

theorem eig6_eq_cos (k : Fin 6) : eig6 k = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) := by
  fin_cases k <;> simp only [eig6] <;> norm_num
  · rw [show 2 * Real.pi / 6 = Real.pi / 3 by ring, Real.cos_pi_div_three]
    norm_num
  · rw [show 2 * Real.pi * 2 / 6 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  · rw [show 2 * Real.pi * 3 / 6 = Real.pi by ring, Real.cos_pi]
    norm_num
  · rw [show 2 * Real.pi * 4 / 6 = 2 * Real.pi - (Real.pi - Real.pi / 3) by ring,
      Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · rw [show 2 * Real.pi * 5 / 6 = 2 * Real.pi - Real.pi / 3 by ring, Real.cos_two_pi_sub,
      Real.cos_pi_div_three]
    norm_num

/-- **Hückel theory for benzene (`C₆`).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₆` is
`∏_{k=0}^{5} (X - 2 cos (2πk/6))`; equivalently, the adjacency eigenvalues of `C₆`,
listed with multiplicity, are `2 cos (2πk/6)` for `k = 0, …, 5`
(namely `2, 1, 1, -1, -1, -2`). -/
