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

theorem is not proved; this is a Lean-checked reduction of it.

The main Mathlib results used are `lp.inner_eq_tsum`,
`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`, `spectrum.nonempty`,
`IsSelfAdjoint.mem_spectrum_eq_re`, `spectrum.norm_le_norm_of_mem`, `spectrum.units_conjugate`,
`IsPreconnected.Icc_subset` and `Perfect.exists_nat_bool_injection`.
-/

open scoped ENNReal InnerProductSpace Topology

namespace Frontier

/-! ## The Hilbert space `ℓ²(ℤ; ℂ)` -/

/-- The Hilbert space `ℓ²(ℤ; ℂ)` on which the almost Mathieu operator acts. -/
noncomputable abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨0, lp.single (E := fun _ : ℤ => ℂ) 2 (0 : ℤ) (1 : ℂ), fun h => ?_⟩
  have h1 : ‖lp.single (E := fun _ : ℤ => ℂ) 2 (0 : ℤ) (1 : ℂ)‖ = 1 := by
    rw [lp.norm_single (by norm_num)]; simp
  rw [← h] at h1
  simp at h1

