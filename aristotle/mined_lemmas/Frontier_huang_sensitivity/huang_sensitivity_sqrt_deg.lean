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

theorem huang_sensitivity_sqrt_deg (f : Q n → Bool) :
    Real.sqrt (bdeg f) ≤ sensitivity f := by
  rcases Nat.eq_zero_or_pos (bdeg f) with h0 | hpos
  · rw [h0]
    simp
  obtain ⟨T, hTcard, hTne⟩ := exists_coeff_ne_zero f hpos
  set d := bdeg f with hdeq
  have hd : T.card = d := hTcard
  set g : Q d → Bool := restrict T hd f with hg
  have hts : topSum g ≠ 0 := by
    rw [hg, topSum_restrict T hd f]
    rcases mul_self_eq_one_iff.1 (sgn_mul_self (fun _ : Fin d => true)) with h1 | h1 <;>
      rw [h1] <;> simpa using hTne
  have hdeg : ¬ HasDegLE g (d - 1) := fun hc => hts (topSum_eq_zero_of_hasDegLE hpos hc)
  have hmain : Real.sqrt d ≤ sensitivity g := huang_sensitivity hpos g hdeg
  refine hmain.trans ?_
  exact_mod_cast sensitivity_restrict_le T hd f

/-- A sanity check: the two-variable `AND` function has degree `2`. -/
