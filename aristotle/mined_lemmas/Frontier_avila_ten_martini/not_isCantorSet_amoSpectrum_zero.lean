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


theorem not_isCantorSet_amoSpectrum_zero (alpha theta : ℝ) :
    ¬ IsCantorSet (amoSpectrum 0 alpha theta) := by
  rintro ⟨-, -, hint, -⟩
  have h1 : Set.Ioo (-2 : ℝ) 2 ⊆ interior (amoSpectrum 0 alpha theta) :=
    interior_maximal (subset_trans Set.Ioo_subset_Icc_self
      (Icc_subset_amoSpectrum_zero alpha theta)) isOpen_Ioo
  have h2 : (0 : ℝ) ∈ interior (amoSpectrum 0 alpha theta) := h1 (by norm_num)
  rw [hint] at h2
  exact h2

end

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

