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

/-
  Brockian/WeylCayley.lean — unitary conjugation of unbounded operators.

  The corpus module of this name was not supplied; this file provides the object
  `conjugatePMap` used by `Brockian.WeylFreeLaplacianCorrected`: the unitary
  conjugate `U T U⁻¹` of a partially defined operator `T`, with domain the image
  `U (dom T)`.
-/
import Mathlib
import Brockian.WeylOperator

namespace Brockian.Weyl.Cayley

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Unitary conjugation of an unbounded operator.** For a unitary
`e : H ≃ₗᵢ[ℂ] K` and a partially defined operator `T` on `H`, the operator
`e ∘ T ∘ e⁻¹` on `K`, defined on the image `e (dom T)`. -/

theorem norm_freeSymbolResolventMultiplier_le {z : Complex} (hz : z.im ≠ 0)
    (xi : Real) :
    ‖freeSymbolResolventMultiplier z xi‖ ≤ |z.im|⁻¹ := by
  rw [freeSymbolResolventMultiplier, norm_inv]
  have hsim : (freeSymbol xi).im = 0 := Complex.ofReal_im _
  have hnorm : |z.im| ≤ ‖freeSymbol xi - z‖ := by
    calc
      |z.im| = |(freeSymbol xi - z).im| := by
        rw [Complex.sub_im, hsim, zero_sub, abs_neg]
      _ ≤ ‖freeSymbol xi - z‖ := Complex.abs_im_le_norm _
  exact (inv_le_inv₀ (norm_pos_iff.mpr (freeSymbol_sub_ne_zero hz xi))
    (abs_pos.mpr hz)).2 hnorm

