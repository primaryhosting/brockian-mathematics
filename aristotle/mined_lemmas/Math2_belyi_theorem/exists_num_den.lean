/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized here

Belyi's theorem is formalized in its genus-zero (polynomial) form, which is the arithmetic heart
of the theorem: the "curve" is the projective line together with a finite set `S` of marked
complex points, and a Belyi map is given by a polynomial `f ∈ ℚ[X]` — viewed as a map
`ℙ¹ → ℙ¹` defined over `ℚ` for which `∞` is totally ramified over `∞`.

`Math2.belyi_theorem` states that the marked points are defined over `ℚ̄` (i.e. all elements of
`S` are algebraic over `ℚ`) if and only if there is a nonconstant such `f` which maps `S` into
`{0, 1}` and all of whose critical values lie in `{0, 1}`, i.e. which is unramified outside
`{0, 1, ∞}`.

The easy direction is elementary. The hard direction is Belyi's algorithm, carried out here in
two stages:

* `Math2.stageA`: composing with minimal polynomials, one finds a nonconstant `f ∈ ℚ[X]` for
  which the images of the marked points and all critical values are rational. Termination is
  measured by `Math2.muA`, a sum of factorials of the degrees of the algebraic numbers involved.
* `Math2.stageB`: a finite set of rationals is collapsed into `{0, 1}` by repeatedly composing
  with the polynomials `c · x^m (1-x)^n` (after an affine change of coordinates), each step
  strictly decreasing the number of relevant rational values.
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

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Critical points and critical values -/

/-- The critical points in `ℂ` of a polynomial with rational coefficients. -/

lemma exists_num_den {lam : ℚ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ lam = (m : ℚ) / ((m : ℚ) + n) := by
  have hnum : 0 < lam.num := Rat.num_pos.2 h0
  have hlt : lam.num < lam.den := Rat.lt_one_iff_num_lt_denom.mp h1
  refine ⟨lam.num.toNat, lam.den - lam.num.toNat, by omega, by omega, ?_⟩
  have hd : ((lam.num.toNat : ℚ) + ((lam.den - lam.num.toNat : ℕ) : ℚ)) = (lam.den : ℚ) := by
    have hle : (lam.num.toNat : ℕ) ≤ lam.den := by omega
    push_cast [Nat.cast_sub hle]
    ring
  rw [hd]
  have hcast : ((lam.num.toNat : ℕ) : ℚ) = (lam.num : ℚ) :=
    mod_cast Int.toNat_of_nonneg (le_of_lt hnum)
  rw [hcast, Rat.num_div_den]

/-- For `0 < lam < 1` rational there is a polynomial with rational coefficients which kills
`0` and `1`, sends `lam` to `1`, and all of whose critical values lie in `{0, 1}`. -/
