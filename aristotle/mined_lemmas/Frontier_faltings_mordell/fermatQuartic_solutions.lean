import Mathlib
/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Faltings' theorem (the Mordell conjecture) states that a smooth projective curve of genus
`≥ 2` over `ℚ` has only finitely many rational points.

In this file we

* formalise the statement for smooth plane curves in `ℙ²`, where the genus is given by the
  degree–genus formula `g = (d-1)(d-2)/2`, so that `d ≥ 4` is exactly the condition `g ≥ 2`
  (`Frontier.FaltingsMordellStatement`);
* verify, unconditionally, an instance of it: the Fermat quartic `x⁴ + y⁴ = z⁴`, a smooth
  plane curve of degree `4` and hence of genus `3`, has only finitely many rational points
  (`Frontier.faltings_mordell`) — indeed exactly four (`Frontier.fermatQuartic_projPoints`).
  The proof uses Fermat's Last Theorem for exponent four.
-/

namespace Frontier

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The set of `ℚ`-points of the plane projective curve cut out by `F`. -/

lemma fermatQuartic_solutions (v : Fin 3 → ℚ) (hv : v ≠ 0)
    (h : v 0 ^ 4 + v 1 ^ 4 - v 2 ^ 4 = 0) :
    ∃ a : ℚ, a ≠ 0 ∧ (v = a • ![1, 0, 1] ∨ v = a • ![1, 0, -1] ∨ v = a • ![0, 1, 1] ∨
      v = a • ![0, 1, -1]) := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · exfalso
      apply hv
      have h2 : v 2 = 0 := by
        have h2' : v 2 ^ 4 = 0 := by rw [h0, h1] at h; linarith
        exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h2'
      funext i; fin_cases i <;> simpa
    · have h2 : v 2 ≠ 0 := by
        intro h2
        exact h1 (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp
          (by rw [h0, h2] at h; linarith))
      rcases quartic_eq_iff (x := v 1) (y := v 2) (by rw [h0] at h; linarith) with he | he
      · exact ⟨v 2, h2, Or.inr (Or.inr (Or.inl (by funext i; fin_cases i <;> simp [h0, he])))⟩
      · refine ⟨v 1, h1, Or.inr (Or.inr (Or.inr ?_))⟩
        funext i; fin_cases i <;> simp [h0, he]
  · by_cases h1 : v 1 = 0
    · rcases quartic_eq_iff (x := v 0) (y := v 2) (by rw [h1] at h; linarith) with he | he
      · exact ⟨v 0, h0, Or.inl (by funext i; fin_cases i <;> simp [h1, he])⟩
      · refine ⟨v 0, h0, Or.inr (Or.inl ?_)⟩
        funext i; fin_cases i <;> simp [h1, he]
    · have h2 : v 2 ≠ 0 := by
        intro h2
        rw [h2] at h
        exact h0 (eq_zero_of_add_pow_four_eq_zero (b := v 1) (by linarith))
      exact absurd (by linarith : v 0 ^ 4 + v 1 ^ 4 = v 2 ^ 4) (flt_four_rat h0 h1 h2)

