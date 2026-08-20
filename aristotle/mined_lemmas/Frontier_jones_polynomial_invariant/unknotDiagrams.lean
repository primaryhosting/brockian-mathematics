import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open LaurentPolynomial

/-! ## The coefficient ring of the Kauffman bracket -/

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KRing : Type := LaurentPolynomial ℤ

/-- The Kauffman variable `A`. -/

noncomputable def unknotDiagrams : LinkDiagrams where
  Diag := ℤ
  bracket n := ((mu ^ n : KRingˣ) : KRing)
  writhe n := n
  R1pos d d' := d' = d + 1
  R1neg d d' := d' = d - 1
  R2 := Eq
  R3 := Eq
  bracket_R1pos := by
    rintro d d' rfl
    rw [zpow_add_one, Units.val_mul, mu_val]; ring
  writhe_R1pos := by rintro d d' rfl; rfl
  bracket_R1neg := by
    rintro d d' rfl
    rw [zpow_sub_one, Units.val_mul, mu_inv_val]; ring
  writhe_R1neg := by rintro d d' rfl; rfl
  bracket_R2 := by rintro d d' rfl; rfl
  writhe_R2 := by rintro d d' rfl; rfl
  bracket_R3 := by rintro d d' rfl; rfl
  writhe_R3 := by rintro d d' rfl; rfl

/-- **The Jones polynomial of the unknot is `1`**, computed from any of its diagrams
`Uₙ` with `n` kinks. -/
