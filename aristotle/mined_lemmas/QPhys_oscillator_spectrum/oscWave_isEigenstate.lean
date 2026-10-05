/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial

namespace QPhys

/-! ## Hermite polynomials over `ℝ`

We reuse Mathlib's (probabilists') Hermite polynomials `Polynomial.hermite : ℕ → ℤ[X]`
(`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`), pushed forward to `ℝ[X]`.
-/

/-- The `n`-th (probabilists') Hermite polynomial, with real coefficients. -/

theorem oscWave_isEigenstate {hbar m omega : ℝ} (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < omega)
    (n : ℕ) :
    IsOscEigenstate hbar m omega (hbar * omega * ((n : ℝ) + 1 / 2)) (oscWave hbar m omega n) := by
  set c := scale hbar m omega with hc
  have hcpos : 0 < c := scale_pos hh hm ho
  have hcsq : c ^ 2 = 2 * m * omega / hbar := scale_sq hh hm ho
  refine ⟨oscWave_ne_zero hh hm ho n, fun x => c * deriv (psi n) (c * x),
    fun x => c ^ 2 * deriv (deriv (psi n)) (c * x), ?_, ?_, ?_⟩
  · intro x
    have hlin : HasDerivAt (fun t : ℝ => c * t) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have := (hasDerivAt_psi n (c * x)).comp x hlin
    rw [deriv_psi n]
    simpa [oscWave, hc, mul_comm] using this
  · intro x
    have hlin : HasDerivAt (fun t : ℝ => c * t) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have := (hasDerivAt_deriv_psi n (c * x)).comp x hlin
    rw [deriv_deriv_psi n]
    have h2 : HasDerivAt (fun x : ℝ => c * deriv (psi n) (c * x))
        (c * ((Dop (Dop (Hr n))).eval (c * x) * Real.exp (-((c * x) ^ 2 / 4)) * c)) x := by
      rw [deriv_psi n]
      exact this.const_mul c
    convert h2 using 1
    ring
  · intro x
    have heig := psi_eigen n (c * x)
    have hsecond : deriv (deriv (psi n)) (c * x)
        = ((c * x) ^ 2 / 4 - ((n : ℝ) + 1 / 2)) * psi n (c * x) := by linarith [heig]
    have hcx : (1 / 2) * m * omega ^ 2 * x ^ 2 = hbar ^ 2 / (2 * m) * c ^ 2 * ((c * x) ^ 2 / 4) := by
      rw [hcsq]
      field_simp
      ring
    have hcoef : hbar ^ 2 / (2 * m) * c ^ 2 = hbar * omega := by
      rw [hcsq]; field_simp; ring
    show -(hbar ^ 2 / (2 * m)) * (c ^ 2 * deriv (deriv (psi n)) (c * x))
      + (1 / 2) * m * omega ^ 2 * x ^ 2 * oscWave hbar m omega n x
      = hbar * omega * ((n : ℝ) + 1 / 2) * oscWave hbar m omega n x
    simp only [oscWave, ← hc]
    rw [hsecond, hcx]
    nlinarith [hcoef, psi n (c * x)]

/-- **Spectrum of the quantum harmonic oscillator.**
For `ℏ, m, ω > 0` the set of energies attained by the ladder-generated (Hermite) eigenfunctions
of `H = -(ℏ²/2m) d²/dx² + (1/2) m ω² x²` is exactly `{ℏω(n + 1/2) : n ∈ ℕ}`. -/
