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

lemma range_Bop_sup_range_Cop (hn : 1 ≤ n) :
    LinearMap.range (Bop n) ⊔ LinearMap.range (Cop n) = ⊤ := by
  have hpos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  refine eq_top_iff.2 (fun w _ => ?_)
  set u : Q n → ℝ := (2 * Real.sqrt n)⁻¹ • w with hu
  have hsum : Bop n u + Cop n u = (2 * Real.sqrt n) • u := by
    rw [Bop_apply, Cop_apply]
    module
  have hw : w = Bop n u + Cop n u := by
    rw [hsum, hu, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  rw [hw]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

