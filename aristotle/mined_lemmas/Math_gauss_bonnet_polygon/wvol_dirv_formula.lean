import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/

lemma wvol_dirv_formula {e f : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    {ψ : ℝ} (h0 : 0 ≤ ψ) (hp : ψ ≤ π) :
    wvol (dirv e f 0) (dirv e f ψ) = 2 / 3 * (π - ψ) := by
  have key := wvol_dirv_eq_Wfun he hf hef (ψ - π / 2) (π / 2)
  rw [show ψ - π / 2 + π / 2 = ψ by ring, show π / 2 - π / 2 = (0 : ℝ) by ring,
    show π / 2 - (ψ - π / 2) = π - ψ by ring, Wfun_eq (by linarith) (by linarith)] at key
  rw [wvol_comm, key]
  ring

/-- There is a unit vector orthogonal to any given unit vector. -/
