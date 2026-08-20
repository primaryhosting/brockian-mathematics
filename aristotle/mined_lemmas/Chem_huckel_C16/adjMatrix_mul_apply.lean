import Mathlib

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

/-- A primitive 16-th root of unity. -/

lemma adjMatrix_mul_apply (M : Matrix (Fin 16) (Fin 16) ℂ) (i k : Fin 16) :
    (C16adj * M) i k = M (i + 1) k + M (i - 1) k := by
  classical
  simp only [C16adj, Matrix.mul_apply, SimpleGraph.adjMatrix_apply]
  have h1 : ∀ j : Fin 16,
      (if (SimpleGraph.cycleGraph 16).Adj i j then (1 : ℂ) else 0) * M j k
        = if (j = i + 1 ∨ j = i - 1) then M j k else 0 := by
    intro j
    by_cases h : (SimpleGraph.cycleGraph 16).Adj i j
    · rw [if_pos h, if_pos ((adj_iff i j).1 h), one_mul]
    · rw [if_neg h, if_neg (fun hh => h ((adj_iff i j).2 hh)), zero_mul]
  have h2 : (Finset.univ : Finset (Fin 16)).filter (fun j => j = i + 1 ∨ j = i - 1)
      = {i + 1, i - 1} := by
    ext j
    simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_filter, h2,
    Finset.sum_pair (succ_ne_pred i)]

