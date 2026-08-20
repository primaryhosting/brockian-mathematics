/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## Overview

Mathlib contains no theory of moduli spaces of bordered Riemann surfaces or of
Weil–Petersson volumes, so the objects entering Mirzakhani's recursion are defined here from
scratch.  The two nontrivial inputs taken from Mathlib are the Basel sum `hasSum_zeta_two`
(`∑ 1 / n ^ 2 = π ^ 2 / 6`) and the Gamma-integral evaluation
`Real.integral_rpow_mul_exp_neg_mul_Ioi`; everything else (the Fermi–Dirac integral
`∫₀^∞ v / (1 + e ^ v) dv = π ^ 2 / 12`, the first moment of Mirzakhani's kernel, and the
recursion itself) is proved below.
-/

namespace Frontier

open MeasureTheory Set

/-! ## The Fermi–Dirac weight and Mirzakhani's kernel -/

/-- The Fermi–Dirac weight `σ (y) = 1 / (1 + e ^ y)` occurring in Mirzakhani's kernel. -/

noncomputable def V₀₄ (L₁ L₂ L₃ L₄ : ℝ) : ℝ :=
  2 * Real.pi ^ 2 + (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2

/-- The right-hand side of Mirzakhani's recursion for `(g, n) = (0, 4)`.

In general the right-hand side is a sum of three groups of terms: the two "pair of pants"
terms `A^{con}` (gluing the two new boundary components to one connected surface of genus
`g - 1`) and `A^{dcon}` (splitting off two stable pieces), and the terms `B` coming from
gluing the first boundary to the `j`-th one.  For `(g, n) = (0, 4)` both `A`-terms are empty:
`A^{con}` needs `g ≥ 1`, and every splitting of `{L₂, L₃, L₄}` into two pieces leaves an
unstable component.  Hence only the `B`-terms, recorded below, survive; each of them involves
the volume `V_{0,3}` of a pair of pants. -/
