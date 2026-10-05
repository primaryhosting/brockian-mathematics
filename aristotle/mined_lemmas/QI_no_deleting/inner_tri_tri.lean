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
