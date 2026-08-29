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

lemma Wfun_eq {θ : ℝ} (h0 : 0 ≤ θ) (hp : θ ≤ π) : Wfun θ = 2 * θ / 3 :=
  additive_linear Wfun_nonneg Wfun_zero (fun _ _ hx hy hxy => Wfun_add hx hy hxy) Wfun_pi h0 hp

