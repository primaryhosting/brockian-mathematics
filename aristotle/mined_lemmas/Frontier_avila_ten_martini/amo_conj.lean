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

theorem amo_conj (lam alpha theta : ℝ) :
    reindexCLM (Equiv.addRight (1 : ℤ)) * amo lam alpha theta
        * reindexCLM (Equiv.addRight (-1 : ℤ)) = amo lam alpha (theta + alpha) := by
  ext x n
  simp only [ContinuousLinearMap.mul_apply, reindexCLM_apply, amo_apply, Equiv.coe_addRight]
  have hV : amoPotential lam alpha theta (n + 1) = amoPotential lam alpha (theta + alpha) n := by
    unfold amoPotential
    have hcos : theta + ((n + 1 : ℤ) : ℝ) * alpha = theta + alpha + (n : ℝ) * alpha := by
      push_cast; ring
    rw [hcos]
  rw [hV, show n + 1 + 1 + -1 = n + 1 from by ring, show n + 1 - 1 + -1 = n - 1 from by ring,
    show n + 1 + -1 = n from by ring]

/-! ## The spectrum of the almost Mathieu operator -/

/-- The spectrum of the almost Mathieu operator, viewed as a subset of `ℝ`
(legitimate since the operator is self-adjoint). -/
