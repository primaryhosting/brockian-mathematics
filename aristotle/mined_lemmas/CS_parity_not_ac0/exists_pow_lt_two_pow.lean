import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

lemma exists_pow_lt_two_pow (k : ℕ) : ∃ L : ℕ, ∀ ℓ, L ≤ ℓ → ℓ ^ k < 2 ^ ℓ := by
  have h2 := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k (r := 2) (by norm_num)).def
    (c := 1 / 2) (by norm_num)
  rw [Filter.eventually_atTop] at h2
  obtain ⟨L, hL⟩ := h2
  refine ⟨L, fun l hl => ?_⟩
  have hl' := hL l hl
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ k),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ l)] at hl'
  have : ((l : ℝ) ^ k) < 2 ^ l := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) l]
  exact_mod_cast this

/-- **PARITY is not in `AC⁰`.** -/
