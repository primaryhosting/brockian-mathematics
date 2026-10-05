/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Deleting

The no-deleting theorem states that, given two copies of an unknown quantum state,
there is no unitary evolution that erases one of the copies (into a fixed "blank"
state), even with the help of an ancilla.

We model a qubit by `EuclideanSpace ℂ (Fin 2)` and the joint system -- two qubit
registers together with an ancilla register indexed by a finite type `A` -- by
`EuclideanSpace ℂ (Fin 2 × Fin 2 × A)`.  The product (unentangled) state
`ψ ⊗ b ⊗ a` is `QI.tri ψ b a`.

A deleting machine would be a unitary `U` on the joint system, together with a
fixed blank state `blank` and a fixed final ancilla state `a₁`, such that

  `U (ψ ⊗ ψ ⊗ a₀) = ψ ⊗ blank ⊗ a₁`   for every unit vector `ψ`.

Since a unitary preserves inner products, this would force `c * c = c * t` for the
overlap `c = ⟪ψ, φ⟫` of any two unit vectors `ψ, φ`, where `t = ⟪blank, blank⟫ *
⟪a₁, a₁⟫`.  Taking `ψ = φ` a unit vector gives `t = 1`, and then `ψ = (1, 0)`,
`φ = (3/5, 4/5)` gives `(3/5)^2 = 3/5`, a contradiction.
-/

namespace QI

open scoped ComplexConjugate

/-- The product state `ψ ⊗ b ⊗ a` of two qubit registers and an ancilla register. -/
noncomputable def tri {A : Type*} [Fintype A] (ψ b : EuclideanSpace ℂ (Fin 2))
    (a : EuclideanSpace ℂ A) : EuclideanSpace ℂ (Fin 2 × Fin 2 × A) :=
  WithLp.toLp 2 fun p => ψ p.1 * b p.2.1 * a p.2.2

private theorem sum_mul_sum_mul_sum {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (F : ι → ℂ) (G : κ → ℂ) (H : μ → ℂ) :
    ∑ i, ∑ j, ∑ k, F i * G j * H k = (∑ i, F i) * (∑ j, G j) * (∑ k, H k) := by
  simp only [← Finset.sum_mul, ← Finset.mul_sum]

/-- Inner products of product states factor as products of the inner products. -/
theorem inner_tri_tri {A : Type*} [Fintype A] (ψ₁ b₁ ψ₂ b₂ : EuclideanSpace ℂ (Fin 2))
    (a₁ a₂ : EuclideanSpace ℂ A) :
    (inner ℂ (tri ψ₁ b₁ a₁) (tri ψ₂ b₂ a₂) : ℂ) =
      (inner ℂ ψ₁ ψ₂ : ℂ) * (inner ℂ b₁ b₂ : ℂ) * (inner ℂ a₁ a₂ : ℂ) := by
  simp only [PiLp.inner_apply, tri, RCLike.inner_apply, map_mul, Fintype.sum_prod_type]
  rw [show (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : A,
      ψ₂ i * b₂ j * a₂ k * ((starRingEnd ℂ) (ψ₁ i) * (starRingEnd ℂ) (b₁ j) *
        (starRingEnd ℂ) (a₁ k))) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : A,
        (ψ₂ i * (starRingEnd ℂ) (ψ₁ i)) * (b₂ j * (starRingEnd ℂ) (b₁ j)) *
          (a₂ k * (starRingEnd ℂ) (a₁ k)) from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring]
  exact sum_mul_sum_mul_sum _ _ _

/-- The qubit state `(1, 0)`. -/
noncomputable def q0 : EuclideanSpace ℂ (Fin 2) := !₂[1, 0]

/-- The qubit state `(3/5, 4/5)`. -/
noncomputable def q1 : EuclideanSpace ℂ (Fin 2) := !₂[3 / 5, 4 / 5]

theorem norm_q0 : ‖q0‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [q0, Fin.sum_univ_two]
  norm_num

theorem norm_q1 : ‖q1‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [q1, Fin.sum_univ_two, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show ((3 / 5 : ℂ)) = ((3 / 5 : ℝ) : ℂ) by norm_num,
    show ((4 / 5 : ℂ)) = ((4 / 5 : ℝ) : ℂ) by norm_num, Complex.norm_real, Complex.norm_real,
    show ‖(3 / 5 : ℝ)‖ ^ 2 + ‖(4 / 5 : ℝ)‖ ^ 2 = 1 by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; norm_num]
  exact Real.sqrt_one

theorem inner_q0_q0 : (inner ℂ q0 q0 : ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_q0]
  norm_num

theorem inner_q0_q1 : (inner ℂ q0 q1 : ℂ) = 3 / 5 := by
  simp [q0, q1, PiLp.inner_apply, Fin.sum_univ_two]

/-- **No-deleting theorem** (isometry version).  There is no linear isometry of the
joint system (two qubit registers plus an ancilla) sending `ψ ⊗ ψ ⊗ a₀` to
`ψ ⊗ blank ⊗ a₁` for every unit vector `ψ`, where the blank state `blank` and the
final ancilla state `a₁` do not depend on `ψ`. -/
theorem no_deleting_isometry {A : Type*} [Fintype A] (a₀ a₁ : EuclideanSpace ℂ A)
    (blank : EuclideanSpace ℂ (Fin 2)) (ha₀ : ‖a₀‖ = 1) :
    ¬ ∃ U : EuclideanSpace ℂ (Fin 2 × Fin 2 × A) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2 × Fin 2 × A),
      ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → U (tri ψ ψ a₀) = tri ψ blank a₁ := by
  rintro ⟨U, hU⟩
  have ha₀' : (inner ℂ a₀ a₀ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, ha₀]; norm_num
  -- The key identity: for unit vectors `ψ, φ`, `⟪ψ, φ⟫ * ⟪ψ, φ⟫ = ⟪ψ, φ⟫ * t`,
  -- where `t = ⟪blank, blank⟫ * ⟪a₁, a₁⟫`.
  have key : ∀ ψ φ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → ‖φ‖ = 1 →
      (inner ℂ ψ φ : ℂ) * (inner ℂ ψ φ : ℂ) =
        (inner ℂ ψ φ : ℂ) * ((inner ℂ blank blank : ℂ) * (inner ℂ a₁ a₁ : ℂ)) := by
    intro ψ φ hψ hφ
    have h := U.inner_map_map (tri ψ ψ a₀) (tri φ φ a₀)
    rw [hU ψ hψ, hU φ hφ, inner_tri_tri, inner_tri_tri, ha₀'] at h
    linear_combination -h
  have h00 := key q0 q0 norm_q0 norm_q0
  rw [inner_q0_q0] at h00
  have ht : (inner ℂ blank blank : ℂ) * (inner ℂ a₁ a₁ : ℂ) = 1 := by
    simpa using h00.symm
  have h01 := key q0 q1 norm_q0 norm_q1
  rw [inner_q0_q1, ht] at h01
  norm_num at h01

/-- **No-deleting theorem.**  There is no unitary evolution of the joint system
(two qubit registers plus an ancilla) that deletes one copy of an unknown quantum
state: no unitary `U` sends `ψ ⊗ ψ ⊗ a₀` to `ψ ⊗ blank ⊗ a₁` for every unit vector
`ψ`, where the blank state `blank` and the final ancilla state `a₁` are fixed
(independent of `ψ`). -/
theorem no_deleting {A : Type*} [Fintype A] (a₀ a₁ : EuclideanSpace ℂ A)
    (blank : EuclideanSpace ℂ (Fin 2)) (ha₀ : ‖a₀‖ = 1) :
    ¬ ∃ U : EuclideanSpace ℂ (Fin 2 × Fin 2 × A) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2 × Fin 2 × A),
      ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → U (tri ψ ψ a₀) = tri ψ blank a₁ := by
  rintro ⟨U, hU⟩
  exact no_deleting_isometry a₀ a₁ blank ha₀ ⟨U.toLinearIsometry, hU⟩

end QI

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

