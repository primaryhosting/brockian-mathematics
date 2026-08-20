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

lemma measureTuple_eq_prod {n : ℕ} (m : ℕ) (f : Bits n → Bits n) (y : Fin m → Bits n) :
    measureTuple m f y = ∏ i, measureFst (simonState f) (y i) := by
  classical
  have h : ∀ z : Fin m → Bits n,
      Complex.normSq (tupleState m f (fun i => (y i, z i)))
        = ∏ i, Complex.normSq (simonState f (y i, z i)) := by
    intro z
    rw [tupleState]
    exact map_prod Complex.normSq _ _
  rw [measureTuple, Finset.sum_congr rfl (fun z _ => h z)]
  simp only [measureFst]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]

/-- The measurement outcome distribution of one run is a genuine probability distribution:
the probabilities sum to `1`. -/
