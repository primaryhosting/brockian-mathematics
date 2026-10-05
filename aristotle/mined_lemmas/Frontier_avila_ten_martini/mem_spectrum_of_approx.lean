import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file formalises the statement of the **Ten Martini Problem** (solved by A. Avila and
S. Jitomirskaya): *for every nonzero coupling constant `λ`, every irrational frequency `α` and
every phase `θ`, the spectrum of the almost Mathieu operator*
`(H u) n = u (n+1) + u (n-1) + 2 λ cos (2π (θ + n α)) u n`
*acting on `ℓ²(ℤ)` is a Cantor set.*

What is proved here, unconditionally:

* the almost Mathieu operator is constructed as a genuine bounded operator on `ℓ²(ℤ)`
  (`Frontier.almostMathieu`), and is shown to be self-adjoint;
* its real spectrum is nonempty, compact (hence closed) and contained in the interval
  `[-(2 + 2|λ|), 2 + 2|λ|]`;
* the elementary symmetries of the family: `α`-periodicity, `θ`-periodicity, the sign change
  `λ ↦ -λ`, and the covariance `H_{λ,α,θ+α} = S H_{λ,α,θ} S⁻¹` under the shift, which gives
  invariance of the spectrum along the orbit of `θ`;
* the **base case `λ = 0`**: via explicit Weyl sequences of truncated plane waves, the spectrum of
  the free discrete Laplacian is shown to contain the whole band `[-2, 2]`, so it is *not* a
  Cantor set (`Frontier.not_isCantorSet_amoSpectrum_zero`).  This shows the hypothesis `λ ≠ 0`
  cannot be dropped from the Ten Martini statement.

The main theorem `Frontier.avila_ten_martini` is a Lean-checked *reduction*: it derives the full
Ten Martini statement (`Frontier.TenMartiniProblem`) from the two deep analytic inputs — that the
spectrum is nowhere dense and that it has no isolated points. All the remaining content of
"being a Cantor set" (nonempty, compact, closed) is proved here from scratch.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Frontier

noncomputable section

open scoped ComplexConjugate

/-- The Hilbert space `ℓ²(ℤ)` of square-summable complex sequences indexed by `ℤ`. -/
abbrev ell2 := lp (fun _ : ℤ => ℂ) 2

/-! ### Basic `ℓ²` facts -/


lemma mem_spectrum_of_approx (T : ell2 →L[ℂ] ell2) (z : ℂ) (M : ℝ) (x : ℕ → ell2)
    (hres : ∀ N, ‖z • x N - T (x N)‖ ≤ M) (hgrow : ∀ C : ℝ, ∃ N, C < ‖x N‖) :
    z ∈ spectrum ℂ T := by
  intro hz
  have hu : IsUnit (algebraMap ℂ (ell2 →L[ℂ] ell2) z - T) := hz
  obtain ⟨u, hu'⟩ := hu
  have hval : ∀ y : ell2, (u : ell2 →L[ℂ] ell2) y = z • y - T y := by
    intro y
    rw [hu']
    simp [Algebra.algebraMap_eq_smul_one]
  have hkey : ∀ N, ‖x N‖ ≤ ‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)‖ * M := by
    intro N
    have h1 : ((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)
        ((u : ell2 →L[ℂ] ell2) (x N)) = x N := by
      have h := congrArg (fun A : ell2 →L[ℂ] ell2 => A (x N)) u.inv_val
      simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using h
    calc ‖x N‖ = ‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)
            ((u : ell2 →L[ℂ] ell2) (x N))‖ := by rw [h1]
      _ ≤ ‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)‖ * ‖(u : ell2 →L[ℂ] ell2) (x N)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)‖ * M := by
          rw [hval]
          exact mul_le_mul_of_nonneg_left (hres N) (norm_nonneg _)
  obtain ⟨N, hN⟩ := hgrow (‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)‖ * M)
  exact absurd (hkey N) (not_le.mpr hN)

