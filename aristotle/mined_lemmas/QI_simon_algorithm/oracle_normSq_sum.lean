/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/

theorem oracle_normSq_sum {n : ℕ} (f : Bits n → Bits n) (psi : Amp n) :
    ∑ p : Bits n × Bits n, Complex.normSq (oracle f psi p)
      = ∑ p : Bits n × Bits n, Complex.normSq (psi p) := by
  classical
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x _
  refine Finset.sum_nbij' (fun z => z - f x) (fun z => z + f x) ?_ ?_ ?_ ?_ ?_
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact Finset.mem_univ _
  · intro z _; simp
  · intro z _; simp
  · intro z _; rfl

/-- The initial state is normalized. -/
