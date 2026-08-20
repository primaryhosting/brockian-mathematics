/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma adj_row_sum (g : Fin 20 → ℂ) (j : Fin 20) :
    (∑ m : Fin 20, ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) j m * g m)
      = g (j - 1) + g (j + 1) := by
  have hne : j - 1 ≠ j + 1 := by
    have h : ∀ i : Fin 20, i - 1 ≠ i + 1 := by decide
    exact h j
  have hterm : ∀ m : Fin 20,
      ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) j m * g m
        = if m ∈ ({j - 1, j + 1} : Finset (Fin 20)) then g m else 0 := by
    intro m
    rw [SimpleGraph.adjMatrix_apply]
    by_cases h : (SimpleGraph.cycleGraph 20).Adj j m
    · rw [if_pos h, one_mul, if_pos]
      simpa using (cycle20_adj_iff j m).mp h
    · rw [if_neg h, zero_mul, if_neg]
      intro hmem
      exact h ((cycle20_adj_iff j m).mpr (by simpa using hmem))
  rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair hne]

/-- The diagonal matrix of Hückel eigenvalues. -/
