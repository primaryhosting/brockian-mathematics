/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-! ### A primitive 7th root of unity -/

/-- A primitive 7th root of unity. -/

theorem huckel_C7 :
    ((cycleGraph 7).adjMatrix ℝ).charpoly
      = ∏ k ∈ Finset.range 7, (X - C (2 * Real.cos (2 * Real.pi * k / 7))) := by
  have hinj : Function.Injective (Polynomial.map (Complex.ofRealHom : ℝ →+* ℂ)) :=
    Polynomial.map_injective _ Complex.ofReal_injective
  apply hinj
  rw [← Matrix.charpoly_map, adjMatrix_map, charpoly_complex]
  rw [Polynomial.map_prod, ← Fin.prod_univ_eq_prod_range
    (fun k : ℕ => Polynomial.map (Complex.ofRealHom : ℝ →+* ℂ)
      (X - C (2 * Real.cos (2 * Real.pi * k / 7)))) 7]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [lam7_eq k]
  simp

/-- Consequently each of the seven numbers `2 cos (2πk/7)`, `k = 0, …, 6`, is an eigenvalue
of the adjacency matrix of `C₇` (a root of its characteristic polynomial). -/
