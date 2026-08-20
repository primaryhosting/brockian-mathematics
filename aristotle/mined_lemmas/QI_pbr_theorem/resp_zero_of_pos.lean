import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

private lemma resp_zero_of_pos (M : OnticModel Λ) (l : Λ) (h0 : 0 < M.mu 0 l)
    (h1 : 0 < M.mu 1 l) (i : Fin 4) : M.resp i (l, l) = 0 := by
  set a := (badPair i).1 with ha
  set b := (badPair i).2 with hb
  have hsum : ∑ p : Λ × Λ, M.mu a p.1 * M.mu b p.2 * M.resp i p = 0 := by
    rw [M.born i a b, ha, hb, born_bad i]
  have hterm : M.mu a l * M.mu b l * M.resp i (l, l) = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ =>
      mul_nonneg (mul_nonneg (M.mu_nonneg a p.1) (M.mu_nonneg b p.2)) (M.resp_nonneg i p))).1
      hsum (l, l) (Finset.mem_univ _)
    simpa using this
  have hpos : 0 < M.mu a l * M.mu b l := by
    have ha' : 0 < M.mu a l := by fin_cases i <;> simp [ha, badPair] <;> assumption
    have hb' : 0 < M.mu b l := by fin_cases i <;> simp [hb, badPair] <;> assumption
    exact mul_pos ha' hb'
  rcases mul_eq_zero.1 hterm with h | h
  · exact absurd h (ne_of_gt hpos)
  · exact h

/-- **Pusey–Barrett–Rudolph theorem.**  In any ontological model of quantum theory
that reproduces the Born-rule statistics of the PBR entangled measurement and
satisfies preparation independence, the distributions of ontic states associated
with the distinct pure states `|0⟩` and `|+⟩` have disjoint supports: no ontic
state `l` is compatible with both preparations.  Hence the quantum state is ontic:
it is a function of the ontic state. -/
