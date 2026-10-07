/-
  QuasiRH003/Targets.lean — OPEN TARGETS.  Contains `sorry` by design; not in the `Brockian`
  lean_lib, not imported, not in the PROVED corpus, not badged (same convention as
  `targets/`).  Each `sorry` is a ProblemCard obligation:
  `pipeline/catalog/math/math-scat5-scattering-pole-band.json`.

  The targets are the nearest objects in the current programme to which the imported
  7/8 strip applies directly: the SL₂(ℤ) scattering function φ(s) and the scattering
  determinant of Γ₀(5).  Their non-elementary poles sit at s = ρ/2 for zeros ρ of ζ, so the
  strip 1/8 ≤ Re ρ ≤ 7/8 confines them to the band 1/16 ≤ Re s ≤ 7/16.

  "Poles" are stated positively — the function is `DifferentiableAt` every point of the open
  strip 0 < Re s < 1/2 OUTSIDE the band — since Mathlib has no meromorphic-pole API.

  Build inside openai/math (imports Import003); see Import003.lean, MODE B.
-/
import Brockian.QuasiRH003Import

open Complex Brockian.QuasiRHTransfer Brockian.QuasiRH003

noncomputable section

namespace Brockian.QuasiRH003.Targets

/-- The scattering function of `SL₂(ℤ)`:
`φ(s) = √π · Γ(s − 1/2) · ζ(2s − 1) / (Γ(s) · ζ(2s))`.
Its poles in `0 < Re s < 1/2` are exactly the points `ρ/2` with `ζ(ρ) = 0`. -/
def scatteringFunction (s : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - 1 / 2) * riemannZeta (2 * s - 1)
    / (Complex.Gamma s * riemannZeta (2 * s))

/-- The scattering determinant of `Γ₀(5)` (cusps ∞ and 0), from the standard explicit
scattering matrix for `Γ₀(p)`:
`det Φ(s) = φ(s)² · (p² + 1 − p^{2s} − p^{2−2s}) / (p^{2s} − 1)²`, with `p = 5`,
`p² + 1 = 26`.  The elementary factor has poles on `Re s = 0` and zeros on
`Re s ∈ {0, 1}`, so it contributes nothing inside the open strip.

CROSS-CHECK the constants against the Fricke-channel derivation in
Structural_Theorems_Pass_3 before relying on them (cusp-width conventions differ between
Hejhal, Huxley and Iwaniec; a wrong convention changes the elementary factor, not the
band).  `M_p(s) · M_p(1 − s) = I` has been checked by hand for this matrix. -/
def scatteringDet5 (s : ℂ) : ℂ :=
  scatteringFunction s ^ 2 * ((26 : ℂ) - (5 : ℂ) ^ (2 * s) - (5 : ℂ) ^ (2 - 2 * s))
    / ((5 : ℂ) ^ (2 * s) - 1) ^ 2

/-- **Target A.**  `φ` is analytic on the open strip `0 < Re s < 1/2` away from the band
`1/16 ≤ Re s ≤ 7/16`.

Route: `Γ(s − 1/2)`, `Γ(s)` differentiable and `Γ(s) ≠ 0` (`Re s > 0`,
`Re (s − 1/2) ∈ (−1/2, 0)`, `s ≠ 1/2`); `ζ(2s − 1)` differentiable (`2s − 1 ≠ 1`);
`ζ(2s)` differentiable (`2s ≠ 1`) and nonzero by `riemannZeta_zero_strip` applied to `2s`,
whose real part lies in `(0, 1)` but outside `[1/8, 7/8]`.  Then the quotient rule. -/
theorem scatteringFunction_differentiableAt_of_outside_band {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1 / 2) (hband : s.re < 1 / 16 ∨ 7 / 16 < s.re) :
    DifferentiableAt ℂ scatteringFunction s := by
  sorry

/-- **Target B.**  The `Γ₀(5)` scattering determinant is analytic on the open strip away from
the same band.  Beyond Target A one needs `5^{2s} ≠ 1`: `‖5^{2s}‖ = 5^{2 Re s} > 1`. -/
theorem scatteringDet5_differentiableAt_of_outside_band {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1 / 2) (hband : s.re < 1 / 16 ∨ 7 / 16 < s.re) :
    DifferentiableAt ℂ scatteringDet5 s := by
  sorry

/-- **Target C (for the record).**  Under RH every pole of `φ` in the open strip lies on
`Re s = 1/4`.  The 7/8 input gives the band; closing the band to the line is RH.  Kept so
the theorem map shows exactly what remains. -/
theorem scatteringFunction_differentiableAt_of_RH
    (hRH : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1 / 2) (hne : s.re ≠ 1 / 4) :
    DifferentiableAt ℂ scatteringFunction s := by
  sorry

end Brockian.QuasiRH003.Targets

end
