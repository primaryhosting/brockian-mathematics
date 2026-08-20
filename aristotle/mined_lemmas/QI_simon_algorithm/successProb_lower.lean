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

theorem successProb_lower {n : ℕ} (f : Bits n → Bits n) (s : Bits n) (hf : SimonPromise f s) :
    (3 : ℝ) / 4 ≤ successProb (n + 2) f s := by
  classical
  have hs : s ≠ 0 := hf.1
  set m := n + 2 with hm
  set K : ℕ := (orth s).card with hK
  have hK2 : 2 * K = 2 ^ n := card_orth s hs
  have hKpos : 0 < K := by
    have : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
    omega
  have hval : ∀ y ∈ goodSet n m s, measureTuple m f y = ((K : ℝ))⁻¹ ^ m := by
    intro y hy
    rw [goodSet, Finset.mem_filter] at hy
    rw [measureTuple_eq_prod]
    have : ∀ i : Fin m, measureFst (simonState f) (y i) = ((K : ℝ))⁻¹ := by
      intro i
      rw [measureFst_simonState f s hf, if_pos (hy.2.1 i)]
      have hKne : ((K : ℝ)) ≠ 0 := by
        have : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
        exact this.ne'
      have h2n : ((2:ℝ)) ^ n = 2 * (K : ℝ) := by exact_mod_cast hK2.symm
      rw [h2n]
      field_simp
    rw [Finset.prod_congr rfl (fun i _ => this i)]
    simp
  rw [successProb, Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hcount := card_goodSet_lower s hs m rfl
  rw [← hK] at hcount
  have hKR : (0:ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hcountR : 3 * (K : ℝ) ^ m ≤ 4 * ((goodSet n m s).card : ℝ) := by
    exact_mod_cast hcount
  have hKm : (0:ℝ) < (K:ℝ) ^ m := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hKm]
  linarith [hcountR]

end QI

/-
The classical query lower bound for Simon's problem: any deterministic classical algorithm
solving Simon's problem needs `Ω(2^(n/2))` queries.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- A deterministic adaptive classical query algorithm: `query` chooses the next query point
from the list of answers received so far, and `out` produces the answer. -/
structure ClassicalAlg (n : ℕ) where
  /-- Choice of the next query, given the answers so far. -/
  query : List (Bits n) → Bits n
  /-- Final output, given the list of answers. -/
  out : List (Bits n) → Bits n

/-- The list of answers received after `k` queries to `f`. -/
