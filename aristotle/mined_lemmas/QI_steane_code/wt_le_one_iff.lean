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

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxRecDepth 100000

namespace QI

namespace Steane

/-! ## The classical `[7,4,3]` Hamming code

`steaneH i j` is the `(i,j)` entry of the parity-check matrix of the Hamming code:
the `i`-th binary digit of the column index `j + 1`.  Explicitly the matrix is

```
1 0 1 0 1 0 1
0 1 1 0 0 1 1
0 0 0 1 1 1 1
```
-/

/-- Parity-check matrix of the classical `[7,4,3]` Hamming code, over `GF(2) = ZMod 2`. -/

theorem wt_le_one_iff (E : PauliErr) : wt E ≤ 1 ↔ ∃ q a b, E = single q a b := by
  classical
  constructor
  · intro h
    rw [wt, Finset.card_le_one_iff_subset_singleton] at h
    obtain ⟨q, hq⟩ := h
    refine ⟨q, E.1 q, E.2 q, ?_⟩
    have key : ∀ j : Fin 7, j ≠ q → E.1 j = 0 ∧ E.2 j = 0 := by
      intro j hj
      by_contra hc
      have hmem : j ∈ Finset.univ.filter (fun j : Fin 7 => E.1 j ≠ 0 ∨ E.2 j ≠ 0) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h1 : E.1 j = 0
        · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
        · exact Or.inl h1
      exact hj (Finset.mem_singleton.mp (hq hmem))
    have h1 : E.1 = Pi.single q (E.1 q) := by
      funext j
      by_cases hj : j = q
      · subst hj; simp
      · rw [Pi.single_eq_of_ne hj, (key j hj).1]
    have h2 : E.2 = Pi.single q (E.2 q) := by
      funext j
      by_cases hj : j = q
      · subst hj; simp
      · rw [Pi.single_eq_of_ne hj, (key j hj).2]
    exact Prod.ext h1 h2
  · rintro ⟨q, a, b, rfl⟩
    rw [wt, Finset.card_le_one_iff_subset_singleton]
    refine ⟨q, ?_⟩
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, single, ne_eq,
      Pi.single_apply] at hj
    simp only [Finset.mem_singleton]
    by_contra hc
    simp [hc] at hj

/-- **Key combinatorial fact.**  Distinct single-qubit Pauli errors have distinct syndromes:
the syndrome map is injective on single-qubit errors. -/
