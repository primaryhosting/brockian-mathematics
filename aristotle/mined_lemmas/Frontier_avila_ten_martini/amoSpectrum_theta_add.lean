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

theorem amoSpectrum_theta_add (lam alpha theta : ℝ) :
    amoSpectrum lam alpha (theta + alpha) = amoSpectrum lam alpha theta := by
  set u : (L2Z →L[ℂ] L2Z)ˣ := reindexUnit (Equiv.addRight (1 : ℤ))
  have hval : (u : L2Z →L[ℂ] L2Z) = reindexCLM (Equiv.addRight (1 : ℤ)) := rfl
  have hinv : ((u⁻¹ : (L2Z →L[ℂ] L2Z)ˣ) : L2Z →L[ℂ] L2Z)
      = reindexCLM (Equiv.addRight (-1 : ℤ)) := by
    show reindexCLM (Equiv.addRight (1 : ℤ)).symm = _
    rw [equiv_addRight_one_symm]
  have h : spectrum ℂ (amo lam alpha (theta + alpha)) = spectrum ℂ (amo lam alpha theta) :=
    calc spectrum ℂ (amo lam alpha (theta + alpha))
        = spectrum ℂ ((u : L2Z →L[ℂ] L2Z) * amo lam alpha theta * (u⁻¹ : (L2Z →L[ℂ] L2Z)ˣ)) := by
          rw [hval, hinv, amo_conj]
      _ = spectrum ℂ (amo lam alpha theta) := spectrum.units_conjugate
  ext E
  simp [amoSpectrum, h]

