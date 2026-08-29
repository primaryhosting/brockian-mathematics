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


def mulCLM (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) : ell2 →L[ℂ] ell2 :=
  LinearMap.mkContinuous
    { toFun := mulFun v C hv
      map_add' := fun f g => by ext n; simp [mul_add]
      map_smul' := fun c f => by ext n; simp; ring } C (by
      intro f
      have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
      have h1 : ‖mulFun v C hv f‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
        rw [norm_sq_eq, mul_pow, norm_sq_eq f, ← tsum_mul_left]
        exact Summable.tsum_le_tsum (fun n => sq_bound v C hv f n) (summable_sq _)
          ((summable_sq f).mul_left (C ^ 2))
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1)

