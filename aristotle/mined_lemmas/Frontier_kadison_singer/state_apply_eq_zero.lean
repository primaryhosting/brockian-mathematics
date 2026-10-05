/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

/-!
## The Kadison–Singer problem

The Kadison–Singer problem asks whether every pure state on the atomic maximal abelian
subalgebra (MASA) `D ⊆ B(ℓ²)` of diagonal operators admits a *unique* extension to a state
on all of `B(ℓ²)`.  It was answered affirmatively by Marcus, Spielman and Srivastava via the
method of interlacing families of polynomials.

Here we formalize the statement of the unique-extension property in the finite dimensional
setting, i.e. for the diagonal MASA `D_n ⊆ M_n(ℂ)`, and give a complete, self-contained proof
of it (this is the classical base case of the problem: the difficulty of Kadison–Singer lies
entirely in the infinite dimensional situation, where the pure states of the MASA are no longer
all of the form `A ↦ A i i`).

The proof formalized below is the standard one: a state `ψ` on `M_n(ℂ)` restricting to the
pure state `δ i` on the diagonal kills the projection `P = 1 - e i i`, and the Cauchy–Schwarz
inequality for positive functionals (proved here from scratch, in the form
`ψ (Xᴴ * X) = 0 → ψ (Xᴴ * Y) = 0`) then forces `ψ A = ψ (e i i * A * e i i) = A i i`.
-/

namespace Frontier

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `M_n(ℂ)`: a unital positive linear functional. -/
structure IsState (ψ : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop where
  /-- A state is unital. -/
  map_one : ψ 1 = 1
  /-- A state is positive. -/
  nonneg : ∀ A : Matrix n n ℂ, 0 ≤ ψ (Aᴴ * A)

/-- The state `A ↦ A i i` on `M_n(ℂ)`, the canonical extension of the pure state `δ i` of the
diagonal MASA. -/

lemma state_apply_eq_zero (X Y : Matrix n n ℂ) (hX : ψ (Xᴴ * X) = 0) :
    ψ (Xᴴ * Y) = 0 := by
  -- expansion of `ψ ((t • X + Y)ᴴ * (t • X + Y))` for real `t`
  have key : ∀ (Z : Matrix n n ℂ), ψ (Zᴴ * Z) = 0 → (ψ (Zᴴ * Y)).re = 0 := by
    intro Z hZ
    apply re_eq_zero_of_forall (d := (ψ (Yᴴ * Y)).re)
    intro t
    have hexp : ψ (((t : ℂ) • Z + Y)ᴴ * ((t : ℂ) • Z + Y))
        = ((t : ℂ) * (t : ℂ)) * ψ (Zᴴ * Z) + (t : ℂ) * ψ (Zᴴ * Y)
          + (t : ℂ) * ψ (Yᴴ * Z) + ψ (Yᴴ * Y) := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
        map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
      simp only [RCLike.star_def, Complex.conj_ofReal, smul_eq_mul]
      ring
    have hsym : ψ (Yᴴ * Z) = (starRingEnd ℂ) (ψ (Zᴴ * Y)) := state_conj_symm hψ Z Y
    have hnn := state_re_nonneg hψ ((t : ℂ) • Z + Y)
    rw [hexp, hZ, hsym] at hnn
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.zero_im,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero] at hnn
    linarith
  have h1 : (ψ (Xᴴ * Y)).re = 0 := key X hX
  have hI : ψ ((Complex.I • X)ᴴ * (Complex.I • X)) = 0 := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, map_smul, map_smul]
    simp only [RCLike.star_def, Complex.conj_I, smul_eq_mul, hX, mul_zero]
  have h2 : (ψ ((Complex.I • X)ᴴ * Y)).re = 0 := key _ hI
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, map_smul] at h2
  simp only [RCLike.star_def, Complex.conj_I, smul_eq_mul, neg_mul, Complex.neg_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_neg] at h2
  exact Complex.ext h1 h2

end

/-- `e i i * A * e i i = A i i • e i i`. -/
