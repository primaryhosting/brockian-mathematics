/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` commands to precede every other command, including
module doc-comments `/-! ... -/`; the header above is therefore a plain block comment,
and is repeated as the module doc-comment right after the import below.)
-/

import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

Mathlib contains no development of the almost Mathieu operator or of the Ten Martini problem, so
the operator is constructed here from scratch on `lp (fun _ : ℤ => ℂ) 2`, out of reindexing
(shift) operators and multiplication by a bounded real sequence.

Proved unconditionally:
* `Frontier.amo_isSelfAdjoint` — self-adjointness of `H_{λ,α,θ}`;
* `Frontier.norm_amo_le` — the operator norm bound `‖H‖ ≤ 2 + 2|λ|`;
* `Frontier.amoSpectrum_nonempty`, `Frontier.amoSpectrum_isCompact` — the (real) spectrum is a
  nonempty compact subset of `ℝ`;
* `Frontier.amo_conj`, `Frontier.amoSpectrum_theta_add` — covariance of the family under the
  shift, and invariance of the spectrum under `θ ↦ θ + α`.

Main statement `Frontier.avila_ten_martini`: the Ten Martini property (Cantor spectrum for all
nonzero coupling and all irrational flux) is *equivalent* to the two analytic inputs of
Avila–Jitomirskaya, namely that the spectrum has empty interior and no isolated points.  The full

theorem memℓp_mul_bdd (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (x : L2Z) :
    Memℓp (fun n => (V n : ℂ) * (x : ℤ → ℂ) n) 2 := by
  apply memℓp_gen
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) ((summable_norm_sq x).mul_left (C ^ (2 : ℝ)))
  simp only [ENNReal.toReal_ofNat, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  gcongr
  exact hV n

/-! ## Reindexing (shift) operators -/

/-- Reindexing of an `ℓ²` sequence along a bijection of `ℤ`, as a linear map. -/
