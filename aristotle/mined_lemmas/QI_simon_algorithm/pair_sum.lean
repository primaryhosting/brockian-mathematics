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

lemma pair_sum {n : ℕ} (f : Bits n → Bits n) (s : Bits n) (hf : SimonPromise f s) (y : Bits n) :
    ∑ x : Bits n, ∑ x' : Bits n, (if f x = f x' then sgn x y * sgn x' y else 0)
      = (2 : ℂ) ^ n * (1 + sgn s y) := by
  classical
  obtain ⟨hs, hfib⟩ := hf
  have hin : ∀ x : Bits n, ∑ x' : Bits n, (if f x = f x' then sgn x y * sgn x' y else 0)
      = 1 + sgn s y := by
    intro x
    have hfilter : (Finset.univ.filter (fun x' : Bits n => f x = f x')) = {x, x + s} := by
      ext x'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [hfib x x']
    rw [← Finset.sum_filter, hfilter]
    have hne : x ≠ x + s := by
      intro hc
      exact hs (left_eq_add.mp hc)
    rw [Finset.sum_pair hne, sgn_add_left, sgn_mul_self]
    rw [← mul_assoc, sgn_mul_self, one_mul]
  rw [Finset.sum_congr rfl (fun x _ => hin x)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [mul_add]

/-! ### The gates of the circuit are unitary -/

