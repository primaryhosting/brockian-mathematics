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

theorem abs_amoPotential_le (lam alpha theta : ℝ) (n : ℤ) :
    |amoPotential lam alpha theta n| ≤ 2 * |lam| := by
  unfold amoPotential
  rw [abs_mul, abs_mul]
  have h1 : |Real.cos (2 * Real.pi * (theta + n * alpha))| ≤ 1 := Real.abs_cos_le_one _
  have h2 : (0 : ℝ) ≤ |(2 : ℝ)| * |lam| := by positivity
  calc |(2 : ℝ)| * |lam| * |Real.cos (2 * Real.pi * (theta + n * alpha))|
      ≤ |(2 : ℝ)| * |lam| * 1 := by gcongr
    _ = 2 * |lam| := by simp

/-- The **almost Mathieu operator** `H_{λ,α,θ}` on `ℓ²(ℤ; ℂ)`:
`(H u)(n) = u(n+1) + u(n-1) + 2 λ cos (2π (θ + n α)) u(n)`. -/
