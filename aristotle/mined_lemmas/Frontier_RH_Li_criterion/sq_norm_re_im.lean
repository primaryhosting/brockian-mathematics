/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Complex Filter

/-! ## Li coefficients of a finite family of zeros -/

/-- The `n`-th **Li coefficient** attached to a finite multiset `Z` of (candidate) zeros:
`λ_n(Z) = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`.  This is the standard Bombieri–Lagarias
expression of Li's coefficients as a sum over the zeros. -/

private theorem sq_norm_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

/-- For `ρ ≠ 0`, the point `ρ` lies on the critical line iff its image `1 - 1/ρ` under the
Möbius transformation carrying the critical line to the unit circle has modulus `1`. -/
