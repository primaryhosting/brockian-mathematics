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

theorem jones_move {d d' : L.Diag} (h : L.Move d d') : L.jones d = L.jones d' := by
  unfold jones
  rcases h with h | h | h | h
  · rw [L.bracket_R1pos d d' h, L.writhe_R1pos d d' h]
    have hw : -(L.writhe d + 1) = -(L.writhe d) - 1 := by ring
    rw [hw, zpow_sub_one, show ((-T 3 : KRing)) = ((mu : KRingˣ) : KRing) from rfl,
      Units.val_mul, mul_assoc,
      ← mul_assoc ((mu⁻¹ : KRingˣ) : KRing) ((mu : KRingˣ) : KRing) (L.bracket d),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  · rw [L.bracket_R1neg d d' h, L.writhe_R1neg d d' h]
    have hw : -(L.writhe d - 1) = -(L.writhe d) + 1 := by ring
    rw [hw, zpow_add_one, show ((-T (-3) : KRing)) = ((mu⁻¹ : KRingˣ) : KRing) from rfl,
      Units.val_mul, mul_assoc,
      ← mul_assoc ((mu : KRingˣ) : KRing) ((mu⁻¹ : KRingˣ) : KRing) (L.bracket d),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  · rw [L.bracket_R2 d d' h, L.writhe_R2 d d' h]
  · rw [L.bracket_R3 d d' h, L.writhe_R3 d d' h]

end LinkDiagrams

/-- **The Jones polynomial is a link invariant.**  The writhe-normalised Kauffman bracket
of a link diagram is unchanged by Reidemeister moves; hence it depends only on the
Reidemeister equivalence class of the diagram, i.e. only on the underlying link. -/
