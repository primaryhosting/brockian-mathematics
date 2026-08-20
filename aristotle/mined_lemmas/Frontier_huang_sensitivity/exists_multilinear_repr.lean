import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

lemma exists_multilinear_repr (g : Q n → ℝ) :
    ∃ p : Finset (Fin n) → ℝ, ∀ x, g x = ∑ T : Finset (Fin n), p T * mono T x := by
  classical
  have hli : LinearIndependent ℝ (fun T : Finset (Fin n) => (mono T : Q n → ℝ)) := by
    refine Fintype.linearIndependent_iff.2 (fun c hc T => ?_)
    refine mono_indep c (fun x => ?_) T
    have := congrFun hc x
    simpa using this
  have hcard : Fintype.card (Finset (Fin n)) = Module.finrank ℝ (Q n → ℝ) := by
    simp [Module.finrank_fintype_fun_eq_card]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = fun T : Finset (Fin n) => (mono T : Q n → ℝ) :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨fun T => b.repr g T, fun x => ?_⟩
  have := b.sum_repr g
  rw [hb] at this
  have := congrFun this x
  simpa [Finset.sum_apply] using this.symm

end Multilinear

section Degree

variable {n : ℕ}

/-- `HasDegLE f d` means that the Boolean function `f` is represented by a multilinear
polynomial with real coefficients all of whose monomials have degree at most `d`. -/
