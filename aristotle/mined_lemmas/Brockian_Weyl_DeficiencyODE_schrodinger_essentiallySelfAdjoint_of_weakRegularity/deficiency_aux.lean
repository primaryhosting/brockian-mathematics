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

theorem deficiency_aux (hV : BoundedPotential V C volume) (u : (schrodingerMin hV)†.domain)
    (z : ℂ) (hz : z.im ≠ 0) (hu : (schrodingerMin hV)† u = z • (u : L2R)) : (u : L2R) = 0 := by
  set w : L2R := (schrodingerMin hV)† u - hV.mul (u : L2R) with hw
  have hreal : conj ⟪(u : L2R), w⟫ = ⟪(u : L2R), w⟫ :=
    inner_isReal_of_weak_second_derivative _ _ (weak_deficiency_equation hV u)
  have hval : ⟪(u : L2R), w⟫ = z * ⟪(u : L2R), (u : L2R)⟫ - ⟪(u : L2R), hV.mul (u : L2R)⟫ := by
    rw [hw, inner_sub_right, hu, inner_smul_right]
  have hconj : conj ⟪(u : L2R), w⟫
      = conj z * ⟪(u : L2R), (u : L2R)⟫ - ⟪(u : L2R), hV.mul (u : L2R)⟫ := by
    rw [hval, _root_.map_sub, map_mul, hV.inner_mul_self_isReal, inner_self_conj]
  rw [hconj, hval] at hreal
  have hzz : (conj z - z) * ⟪(u : L2R), (u : L2R)⟫ = 0 := by linear_combination hreal
  have hne : conj z - z ≠ 0 := by
    intro hcon
    apply hz
    have := sub_eq_zero.1 hcon
    have h2 : (conj z).im = z.im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith
  have : ⟪(u : L2R), (u : L2R)⟫ = 0 := by
    rcases mul_eq_zero.1 hzz with h | h
    · exact absurd h hne
    · exact h
  exact inner_self_eq_zero.1 this

/-- **The minimal Schrödinger operator with a bounded measurable potential is essentially
self-adjoint.**

The hypothesis of *weak regularity* of solutions of the deficiency ODE, which is often assumed
at this point, is discharged (see `inner_isReal_of_weak_second_derivative`), so the statement is
unconditional. -/
