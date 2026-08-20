/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph whose vertices carry a linear order:
the sum of the graph distances over all unordered pairs of distinct vertices
(each pair `{u, v}` counted once, via `u < v`). -/

theorem wiener_path_formula (n : ℕ) :
    wienerIndex (pathGraph n) = (n + 1).choose 3 := by
  rw [wienerIndex, Finset.sum_filter, Fintype.sum_prod_type]
  have key : ∀ i : Fin n, (∑ j : Fin n, if i < j then (pathGraph n).dist i j else 0)
      = ∑ j ∈ Finset.range n, (if (i : ℕ) < j then j - (i : ℕ) else 0) := by
    intro i
    rw [← Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) < j then j - (i : ℕ) else 0) n]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hij : (i : ℕ) < (j : ℕ)
    · rw [if_pos (Fin.lt_def.2 hij), if_pos hij, pathGraph_dist i j (le_of_lt hij)]
    · rw [if_neg (fun h => hij (Fin.lt_def.1 h)), if_neg hij]
  rw [Finset.sum_congr rfl (fun i _ => key i),
    Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, (if i < j then j - i else 0)) n]
  exact sum_pairs_diff n

end Chem

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

