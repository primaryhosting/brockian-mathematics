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

lemma adj_mul_row (i : Fin 7) (f : Fin 7 → ℂ) :
    ∑ j, ((cycleGraph 7).adjMatrix ℂ) i j * f j = f (i - 1) + f (i + 1) := by
  have h1 : ∀ j, ((cycleGraph 7).adjMatrix ℂ) i j * f j
      = if (cycleGraph 7).Adj i j then f j else 0 := by
    intro j; simp [SimpleGraph.adjMatrix_apply]
  simp only [h1, ← Finset.sum_filter, cyc7_filter i]
  rw [Finset.sum_pair (cyc7_ne i)]

/-! ### Diagonalisation -/

/-- The `k`-th Hückel eigenvalue, written in terms of the root of unity `w7`. -/
