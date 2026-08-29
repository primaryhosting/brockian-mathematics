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
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/

lemma card_monomials_le (k : ℕ) :
    #{A : Finset (Fin n) | A.card ≤ k} ≤ ∑ i ∈ range (k + 1), n.choose i := by
  classical
  have hsub : ({A : Finset (Fin n) | A.card ≤ k} : Finset (Finset (Fin n)))
      ⊆ (range (k + 1)).biUnion fun i => Finset.powersetCard i (univ : Finset (Fin n)) := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨A.card, by omega, Finset.subset_univ _, rfl⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.card_powersetCard, Finset.card_fin]

