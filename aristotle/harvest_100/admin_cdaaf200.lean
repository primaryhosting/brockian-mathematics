/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
in units where `α = 0` and `β = 1`). -/
def C3adj : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 1; 1, 0, 1; 1, 1, 0]

/-- The `k`-th Hückel eigenvalue of `C₃`: `2·cos(2πk/3)`. -/
noncomputable def C3eigenvalue (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / 3)

lemma C3eigenvalue_zero : C3eigenvalue 0 = 2 := by
  simp [C3eigenvalue]

lemma C3eigenvalue_one : C3eigenvalue 1 = -1 := by
  have h : (2 * Real.pi * (1 : ℕ) / 3) = Real.pi - Real.pi / 3 := by push_cast; ring
  simp only [C3eigenvalue, h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma C3eigenvalue_two : C3eigenvalue 2 = -1 := by
  have h : (2 * Real.pi * (2 : ℕ) / 3) = Real.pi + Real.pi / 3 := by push_cast; ring
  simp only [C3eigenvalue, h, Real.cos_add, Real.cos_pi, Real.sin_pi,
    Real.cos_pi_div_three]
  norm_num

/-- **Hückel theory for the cyclopropenyl system.**
A real number `x` is an eigenvalue of the adjacency matrix of the cycle graph `C₃`
if and only if it is of the form `2·cos(2πk/3)` for some `k ∈ {0, 1, 2}`. -/
theorem huckel_C3 (x : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = x • v) ↔
      ∃ k : Fin 3, x = C3eigenvalue (k : ℕ) := by
  have key : (∃ k : Fin 3, x = C3eigenvalue (k : ℕ)) ↔ (x = 2 ∨ x = -1) := by
    constructor
    · rintro ⟨k, rfl⟩
      fin_cases k
      · exact Or.inl C3eigenvalue_zero
      · exact Or.inr C3eigenvalue_one
      · exact Or.inr C3eigenvalue_two
    · rintro (rfl | rfl)
      · exact ⟨0, C3eigenvalue_zero.symm⟩
      · exact ⟨1, C3eigenvalue_one.symm⟩
  rw [key]
  constructor
  · rintro ⟨v, hv, h⟩
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    have e2 := congrFun h 2
    simp [C3adj, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e0 e1 e2
    by_cases hs : v 0 + v 1 + v 2 = 0
    · right
      have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hv (funext fun i => by fin_cases i <;> simp [hc.1, hc.2.1, hc.2.2])
      rcases hne with h0 | h0 | h0
      · have : (x + 1) * v 0 = 0 := by linarith [e0]
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · exact absurd h' h0
      · have : (x + 1) * v 1 = 0 := by linarith [e1]
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · exact absurd h' h0
      · have : (x + 1) * v 2 = 0 := by linarith [e2]
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · exact absurd h' h0
    · left
      have : (x - 2) * (v 0 + v 1 + v 2) = 0 := by nlinarith [e0, e1, e2]
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · exact absurd h' hs
  · rintro (rfl | rfl)
    · refine ⟨![1, 1, 1], ?_, ?_⟩
      · intro hc
        have := congrFun hc 0
        norm_num at this
      · funext i
        fin_cases i <;>
          simp [C3adj, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
    · refine ⟨![1, -1, 0], ?_, ?_⟩
      · intro hc
        have := congrFun hc 0
        norm_num at this
      · funext i
        fin_cases i <;>
          simp [C3adj, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

end Chem

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

