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

theorem moebius_one_sub {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    (1 - 1 / (1 - ρ)) * (1 - 1 / ρ) = 1 := by
  have h2 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  field_simp
  ring

/-! ## A simultaneous approximation lemma -/

/-- Simultaneous Dirichlet-type approximation: for finitely many complex numbers of modulus
one there are arbitrarily large exponents `n` making all the powers `w i ^ n` simultaneously
close to `1`. -/
