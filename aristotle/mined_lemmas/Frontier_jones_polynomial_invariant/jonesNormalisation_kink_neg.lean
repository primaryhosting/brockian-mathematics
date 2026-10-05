/-
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false

/-!
## Overview

The Jones polynomial of a link is defined from a *diagram* by the Kauffman bracket state sum
together with the writhe normalisation, and the content of the theorem "the Jones polynomial is a
link invariant" is exactly that this recipe is unchanged by the three Reidemeister moves.

By Kauffman's argument, all three moves reduce to purely *local, algebraic* identities in the
Temperley–Lieb algebra `TL` (with loop parameter `d = -A^2 - A^{-2}`), where the crossing is
resolved as the Kauffman element `σᵢ = A·1 + A⁻¹·eᵢ`:

* **Reidemeister I**: a positive kink multiplies the bracket by `A·d + A⁻¹ = -A^3`
  (and a negative kink by `-A^{-3}`); the writhe normalisation `(-A^3)^{-w}⟨·⟩` cancels this,
  which is what makes the Jones polynomial (as opposed to the bracket) invariant.
* **Reidemeister II**: `σᵢ · σᵢ⁻¹ = 1`, i.e. the Kauffman element is invertible with inverse the
  opposite crossing `A⁻¹·1 + A·eᵢ`.
* **Reidemeister III**: the braid relation `σ₀σ₁σ₀ = σ₁σ₀σ₁`.

This file constructs the Temperley–Lieb algebra on two generators as an honest (associative, unital)
`R`-algebra, proves it is nontrivial by exhibiting a two-dimensional representation, and proves all
of the above identities, culminating in `Frontier.jones_polynomial_invariant`.

Mathlib has no knot theory, so no existing lemma closes this; the algebraic infrastructure
(`RingQuot`, `FreeAlgebra`, `Matrix`) is what is reused.
-/

open FreeAlgebra

namespace Frontier

variable {R : Type*} [CommRing R]

/-! ### The Temperley–Lieb algebra -/

/-- The Temperley–Lieb relations on two generators `e₀, e₁` with loop value `d`:
`eᵢ² = d·eᵢ`, `e₀e₁e₀ = e₀`, `e₁e₀e₁ = e₁`. -/
inductive TLRel (d : R) : FreeAlgebra R (Fin 2) → FreeAlgebra R (Fin 2) → Prop
  | sq (i : Fin 2) : TLRel d (ι R i * ι R i) (d • ι R i)
  | braid₀ : TLRel d (ι R 0 * ι R 1 * ι R 0) (ι R 0)
  | braid₁ : TLRel d (ι R 1 * ι R 0 * ι R 1) (ι R 1)

/-- The Temperley–Lieb algebra `TL₃` on two generators over `R` with loop value `d`. -/
abbrev TL (d : R) := RingQuot (TLRel d)

/-- The Temperley–Lieb generator `eᵢ` (the "cup–cap" planar tangle). -/

theorem jonesNormalisation_kink_neg (A Ai : R) (h : A * Ai = 1) (w : ℤ) (br : R) :
    jonesNormalisation A Ai h (w - 1) ((-Ai ^ 3) * br) = jonesNormalisation A Ai h w br := by
  have hval : (((kauffmanUnit A Ai h)⁻¹ : Rˣ) : R) = -Ai ^ 3 := rfl
  have key : kauffmanUnit A Ai h ^ (-(w - 1)) * (kauffmanUnit A Ai h)⁻¹
      = kauffmanUnit A Ai h ^ (-w) := by
    rw [show (-(w - 1) : ℤ) = -w + 1 by ring, zpow_add_one, mul_inv_cancel_right]
  unfold jonesNormalisation
  rw [← hval, ← mul_assoc, ← Units.val_mul, key]

/-! ### Reidemeister II and III -/

/-- **Reidemeister II.** The Kauffman resolution of a crossing is invertible, with inverse the
resolution of the opposite crossing: `σᵢ · σᵢ⁻¹ = 1`. -/
