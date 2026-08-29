import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    have h0i : 0 ≤ a i := h0 i (Finset.mem_cons_self i s)
    have h1i : a i ≤ 1 := h1 i (Finset.mem_cons_self i s)
    have h0' : ∀ j ∈ s, 0 ≤ a j := fun j hj => h0 j (Finset.mem_cons_of_mem hj)
    have h1' : ∀ j ∈ s, a j ≤ 1 := fun j hj => h1 j (Finset.mem_cons_of_mem hj)
    have ihh := ih h0' h1'
    have hprod : 0 ≤ ∏ j ∈ s, (1 - a j) :=
      Finset.prod_nonneg fun j hj => by linarith [h1' j hj]
    have hsum : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg h0'
    rw [Finset.sum_cons, Finset.prod_cons]
    nlinarith [ihh, hprod, hsum, h0i, h1i]

