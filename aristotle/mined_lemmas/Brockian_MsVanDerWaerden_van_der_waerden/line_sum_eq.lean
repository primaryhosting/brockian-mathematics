import Mathlib
namespace Brockian.MsVanDerWaerden

open Combinatorics Finset

/-- The set of "moving" coordinates of a combinatorial line. -/

private lemma line_sum_eq {k : ℕ} {ι : Type} [Fintype ι] (l : Line (Fin k) ι) (x : Fin k) :
    ∑ i, ((l x i : ℕ)) = lineConst l + (x : ℕ) * (movingSet l).card := by
  simp [lineConst, movingSet]
  rw [← Finset.sum_filter_add_sum_filter_not (p := fun i => l.idxFun i ≠ none)]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp at hi
    cases h : l.idxFun i <;> simp_all
  · simp only [not_not]
    have heq : ∀ i ∈ Finset.univ.filter (fun i => l.idxFun i = none),
        ((l.idxFun i).getD x : ℕ) = x := by
      intro i hi
      simp [Finset.mem_filter.mp hi]
    rw [Finset.sum_congr rfl heq, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The sum of the coordinates of a point of the hypercube `ι → Fin k` is at most
`Fintype.card ι * k`. -/
