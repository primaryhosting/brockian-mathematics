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

import Mathlib

/-!
# The Fourier transform of the Laplacian on Schwartz space

We record the classical formula `𝓕 (Δ f) ξ = -(4π²‖ξ‖²) 𝓕 f ξ` for Schwartz functions,
introduce the Fourier symbol `freeSymbol ξ = 4π²‖ξ‖²` of the free Laplacian `-Δ`, and show that
the "resolvent multiplier" `ξ ↦ (1 + freeSymbol ξ)⁻¹` has temperate growth (so that multiplying
a Schwartz function by it produces again a Schwartz function).
-/

namespace Brockian

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


theorem mulOp_freeSymbol_schwartz (f g : 𝓢(V, ℂ)) (h : ∀ ξ, (freeSymbol ξ : ℂ) * f ξ = g ξ) :
    ∃ hmem : (schwartzToL2 f : L2 V) ∈ (mulOp (freeSymbol : V → ℝ)).domain,
      mulOp freeSymbol ⟨schwartzToL2 f, hmem⟩ = schwartzToL2 g := by
  have hae : (fun ξ => (freeSymbol ξ : ℂ) * ((schwartzToL2 f : L2 V) : V → ℂ) ξ)
      =ᵐ[volume] ((schwartzToL2 g : L2 V) : V → ℂ) := by
    filter_upwards [coeFn_schwartzToL2 f, coeFn_schwartzToL2 g] with ξ h1 h2
    rw [h1, h2, h ξ]
  have hmem : (schwartzToL2 f : L2 V) ∈ (mulOp (freeSymbol : V → ℝ)).domain :=
    (Lp.memLp (schwartzToL2 g)).ae_eq hae.symm
  exact ⟨hmem, mulOp_eq_of_ae _ ⟨schwartzToL2 f, hmem⟩ (schwartzToL2 g) hae.symm⟩

/-- Every Schwartz function lies in the domain of the multiplication operator by the symbol. -/
