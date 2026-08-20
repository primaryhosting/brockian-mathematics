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

theorem norm_amo_le (lam alpha theta : ℝ) : ‖amo lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  refine le_trans (norm_add_le _ _) ?_
  have h1 := norm_reindexCLM_le (Equiv.addRight (1 : ℤ))
  have h2 := norm_reindexCLM_le (Equiv.addRight (-1 : ℤ))
  have h3 := norm_mulCLM_le (amoPotential lam alpha theta) (2 * |lam|)
    (abs_amoPotential_le lam alpha theta)
  have h4 : ‖reindexCLM (Equiv.addRight (1 : ℤ)) + reindexCLM (Equiv.addRight (-1 : ℤ))‖ ≤ 2 :=
    le_trans (norm_add_le _ _) (by linarith)
  linarith

