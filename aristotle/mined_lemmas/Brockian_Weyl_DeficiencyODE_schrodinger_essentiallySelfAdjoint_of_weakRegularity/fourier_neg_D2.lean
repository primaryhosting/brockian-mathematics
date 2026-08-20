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
Essential self-adjointness via the basic criterion on deficiency subspaces.

This file develops, for an unbounded (partially defined) operator on a complex Hilbert
space, the classical criterion of von Neumann/Weyl:

  a densely defined symmetric operator `T` is essentially self-adjoint as soon as the two
  deficiency subspaces `ker (T† - i)` and `ker (T† + i)` are trivial.

Along the way we show that under this hypothesis the closure of `T` coincides with the
adjoint `T†`.
-/
import Mathlib

namespace Brockian.Weyl

open LinearPMap Complex
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- An unbounded operator on a Hilbert space is *essentially self-adjoint* if its closure is
self-adjoint. -/

theorem fourier_neg_D2 (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓕 (-(D2 f)) x = (symb x : ℂ) * 𝓕 f x := by
  have hD2 : 𝓕 (D2 f) x = (-(symb x) : ℝ) * 𝓕 f x := by
    rw [show D2 f = SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f) from rfl,
      fourier_derivCLM, fourier_derivCLM]
    simp only [smul_eq_mul, symb]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hneg : 𝓕 (-(D2 f)) x = -(𝓕 (D2 f) x) := by
    have : (𝓕 (-(D2 f)) : 𝓢(ℝ, ℂ)) = -(𝓕 (D2 f) : 𝓢(ℝ, ℂ)) := map_neg (fourierCLM ℂ _) _
    rw [this]; rfl
  rw [hneg, hD2]
  push_cast
  ring

section Schrodinger

variable {V : ℝ → ℝ} {C : ℝ}

/-- The Schrödinger expression `-f'' + V f`, as a map from Schwartz functions to `L²`. -/
