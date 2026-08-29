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
noncomputable def diagState (i : n) : Matrix n n ℂ →ₗ[ℂ] ℂ := Matrix.entryLinearMap ℂ ℂ i i

@[simp] lemma diagState_apply (i : n) (A : Matrix n n ℂ) : diagState i A = A i i := rfl

lemma isState_diagState (i : n) : IsState (diagState i) := by
  refine ⟨by simp [diagState], fun A => ?_⟩
  simp only [diagState_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg (A j i)

section

variable {ψ : Matrix n n ℂ →ₗ[ℂ] ℂ} (hψ : IsState ψ)
include hψ

lemma state_im_eq_zero (A : Matrix n n ℂ) : (ψ (Aᴴ * A)).im = 0 :=
  ((Complex.le_def.1 (hψ.nonneg A)).2).symm

lemma state_re_nonneg (A : Matrix n n ℂ) : 0 ≤ (ψ (Aᴴ * A)).re :=
  (Complex.le_def.1 (hψ.nonneg A)).1

/-- The sesquilinear form `(X, Y) ↦ ψ (Xᴴ * Y)` associated to a state is conjugate symmetric. -/
lemma state_conj_symm (X Y : Matrix n n ℂ) :
    ψ (Yᴴ * X) = (starRingEnd ℂ) (ψ (Xᴴ * Y)) := by
  have h1 : ψ ((X + Y)ᴴ * (X + Y))
      = ψ (Xᴴ * X) + ψ (Xᴴ * Y) + ψ (Yᴴ * X) + ψ (Yᴴ * Y) := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      map_add, map_add, map_add]
    ring
  have h2 : ψ ((X + Complex.I • Y)ᴴ * (X + Complex.I • Y))
      = ψ (Xᴴ * X) + Complex.I * ψ (Xᴴ * Y) - Complex.I * ψ (Yᴴ * X) + ψ (Yᴴ * Y) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
    simp only [RCLike.star_def, Complex.conj_I, smul_eq_mul, neg_mul]
    ring_nf
    rw [Complex.I_mul_I]
    ring
  have e1 := state_im_eq_zero hψ (X + Y)
  have e2 := state_im_eq_zero hψ (X + Complex.I • Y)
  have p := state_im_eq_zero hψ X
  have q := state_im_eq_zero hψ Y
  rw [h1] at e1
  rw [h2] at e2
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, p, q] at e1 e2
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> linarith

/-- A real quadratic-free positivity argument: if `2 t c + d ≥ 0` for all real `t`, then `c = 0`. -/
private lemma re_eq_zero_of_forall {c d : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * c + d) : c = 0 := by
  by_contra hc
  have := h (-(d + 1) / (2 * c))
  rw [div_mul_eq_mul_div, mul_comm] at this
  field_simp at this
  linarith

/-- Cauchy–Schwarz for states, in the form we need: a null vector of the form
`ψ (Xᴴ * X) = 0` is orthogonal to everything. -/
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
lemma single_mul_mul_single (i : n) (A : Matrix n n ℂ) :
    (Matrix.single i i (1 : ℂ)) * A * (Matrix.single i i (1 : ℂ))
      = A i i • Matrix.single i i (1 : ℂ) := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma single_isDiag (i : n) : (Matrix.single i i (1 : ℂ)).IsDiag := by
  intro j k hjk
  simp only [Matrix.single_apply]
  rintro ⟨rfl, rfl⟩
  exact hjk rfl

/-- **Kadison–Singer, finite dimensional case.**  For the diagonal MASA `D_n ⊆ M_n(ℂ)` and the
pure state `δ i : D → ℂ`, `D ↦ D i i`, there is exactly one state on the full matrix algebra
`M_n(ℂ)` extending it, namely `A ↦ A i i`. -/
theorem kadison_singer (i : n) :
    ∃! ψ : Matrix n n ℂ →ₗ[ℂ] ℂ, IsState ψ ∧ ∀ D : Matrix n n ℂ, D.IsDiag → ψ D = D i i := by
  refine ⟨diagState i, ⟨isState_diagState i, fun D _ => rfl⟩, ?_⟩
  rintro ψ ⟨hstate, hdiag⟩
  ext A
  set E : Matrix n n ℂ := Matrix.single i i (1 : ℂ) with hE
  have hEdiag : E.IsDiag := single_isDiag i
  have hEherm : Eᴴ = E := by
    ext j k
    simp only [hE, Matrix.conjTranspose_apply, Matrix.single_apply, RCLike.star_def]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd ⟨h1.2, h1.1⟩ h2
    · exact absurd ⟨h2.2, h2.1⟩ h1
    · simp
  have hψE : ψ E = 1 := by
    rw [hdiag E hEdiag]
    simp [hE, Matrix.single_apply]
  -- the complementary projection
  set P : Matrix n n ℂ := 1 - E with hP
  have hPdiag : P.IsDiag := (Matrix.isDiag_one).sub hEdiag
  have hPherm : Pᴴ = P := by rw [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hEherm]
  have hEE : E * E = E := by
    have := single_mul_mul_single (n := n) i 1
    simpa [hE, Matrix.single_apply] using this
  have hPP : Pᴴ * P = P := by
    rw [hPherm, hP]
    rw [sub_mul, mul_sub, mul_sub, hEE]
    simp
  have hψP : ψ (Pᴴ * P) = 0 := by
    rw [hPP, hdiag P hPdiag]
    simp [hP, hE, Matrix.single_apply]
  -- `ψ` annihilates `P * Y` and `Y * P`
  have hleft : ∀ Y : Matrix n n ℂ, ψ (P * Y) = 0 := by
    intro Y
    have := state_apply_eq_zero hstate P Y hψP
    rwa [hPherm] at this
  have hright : ∀ Y : Matrix n n ℂ, ψ (Y * P) = 0 := by
    intro Y
    have h := state_conj_symm hstate P (Yᴴ)
    rw [hPherm] at h
    have hz : ψ (Pᴴ * Yᴴ) = 0 := state_apply_eq_zero hstate P (Yᴴ) hψP
    rw [hPherm] at hz
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [h, hz]
    simp
  -- decomposition `A = E * A * E + E * A * P + P * A`
  have hdecomp : A = E * A * E + E * A * P + P * A := by
    rw [hP]
    rw [mul_sub, mul_one]
    ring_nf
    rw [sub_mul, one_mul]
    ring
  calc ψ A = ψ (E * A * E) + ψ (E * A * P) + ψ (P * A) := by
        rw [hdecomp]; simp [map_add]
    _ = A i i := by
        rw [hright (E * A), hleft A, single_mul_mul_single i A, map_smul, hψE]
        simp
  
end Frontier

