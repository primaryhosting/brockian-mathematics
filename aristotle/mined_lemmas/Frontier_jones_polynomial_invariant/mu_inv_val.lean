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

@[simp] lemma mu_inv_val : ((mu⁻¹ : KRingˣ) : KRing) = -T (-3) := rfl

/-- Abstract data of a family of link diagrams equipped with a Kauffman bracket and a
writhe, satisfying exactly the behaviour under the three Reidemeister moves that is
forced by Kauffman's skein relations (see `kauffman_kink_pos`, `kauffman_kink_neg`,
`kauffman_R2`, `kauffman_R3`): a Reidemeister I move multiplies the bracket by `-A^{±3}`
and changes the writhe by `±1`, while Reidemeister II and III moves change neither the
bracket nor the writhe. -/
structure LinkDiagrams where
  /-- The type of link diagrams. -/
  Diag : Type
  /-- The Kauffman bracket of a diagram. -/
  bracket : Diag → KRing
  /-- The writhe of a diagram. -/
  writhe : Diag → ℤ
  /-- Adding a positive kink (Reidemeister I). -/
  R1pos : Diag → Diag → Prop
  /-- Adding a negative kink (Reidemeister I). -/
  R1neg : Diag → Diag → Prop
  /-- A Reidemeister II move. -/
  R2 : Diag → Diag → Prop
  /-- A Reidemeister III move. -/
  R3 : Diag → Diag → Prop
  bracket_R1pos : ∀ d d' : Diag, R1pos d d' → bracket d' = (-T 3) * bracket d
  writhe_R1pos : ∀ d d' : Diag, R1pos d d' → writhe d' = writhe d + 1
  bracket_R1neg : ∀ d d' : Diag, R1neg d d' → bracket d' = (-T (-3)) * bracket d
  writhe_R1neg : ∀ d d' : Diag, R1neg d d' → writhe d' = writhe d - 1
  bracket_R2 : ∀ d d' : Diag, R2 d d' → bracket d' = bracket d
  writhe_R2 : ∀ d d' : Diag, R2 d d' → writhe d' = writhe d
  bracket_R3 : ∀ d d' : Diag, R3 d d' → bracket d' = bracket d
  writhe_R3 : ∀ d d' : Diag, R3 d d' → writhe d' = writhe d

namespace LinkDiagrams

variable (L : LinkDiagrams)

/-- A single Reidemeister move relating two diagrams. -/
