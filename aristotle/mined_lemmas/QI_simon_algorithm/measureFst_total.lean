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

theorem measureFst_total {n : ℕ} (f : Bits n → Bits n) (s : Bits n) (hf : SimonPromise f s) :
    ∑ y : Bits n, measureFst (simonState f) y = 1 := by
  classical
  have hs : s ≠ 0 := hf.1
  rw [Finset.sum_congr rfl (fun y _ => measureFst_simonState f s hf y)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hfil : (Finset.univ.filter (fun y : Bits n => bdot y s = 0)) = orth s := rfl
  rw [hfil]
  have hK2 : 2 * (orth s).card = 2 ^ n := card_orth s hs
  have hKR : ((orth s).card : ℝ) * 2 = 2 ^ n := by exact_mod_cast (by omega : (orth s).card * 2 = 2 ^ n)
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  field_simp
  linarith [hKR]

/-- The outcome tuple `y` pins down the hidden shift `s`: every `y i` is orthogonal to `s`,
and `s` is the only nonzero string with this property. -/
