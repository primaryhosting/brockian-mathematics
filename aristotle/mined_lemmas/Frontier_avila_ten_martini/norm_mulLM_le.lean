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

theorem norm_mulLM_le (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (x : L2Z) :
    ‖mulLM V C hV x‖ ≤ C * ‖x‖ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hV 0)
  refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
  have hsum : Summable (fun n : ℤ => ‖((mulLM V C hV x : L2Z) : ℤ → ℂ) n‖ ^ (2 : ℝ)) := by
    simpa using summable_norm_sq (mulLM V C hV x)
  have hle : ∀ n : ℤ, ‖((mulLM V C hV x : L2Z) : ℤ → ℂ) n‖ ^ (2 : ℝ)
      ≤ C ^ (2 : ℝ) * ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ) := by
    intro n
    simp only [mulLM_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
    gcongr
    exact hV n
  have h1 : ∑' n : ℤ, ‖((mulLM V C hV x : L2Z) : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' n : ℤ, C ^ (2 : ℝ) * ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ) := by
    refine Summable.tsum_le_tsum ?_ (by simpa using hsum) ((summable_norm_sq x).mul_left _)
    simpa using hle
  have hx : ∑' n : ℤ, ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ) = ‖x‖ ^ (2 : ℝ) := by
    simpa using (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x).symm
  refine h1.trans (le_of_eq ?_)
  rw [tsum_mul_left, hx]
  simp only [ENNReal.toReal_ofNat]
  rw [Real.mul_rpow hC (norm_nonneg _)]

/-- Multiplication by a bounded real sequence, as a continuous linear map on `ℓ²(ℤ; ℂ)`. -/
