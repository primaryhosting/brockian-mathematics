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

theorem inner_q0_q0 : (inner ℂ q0 q0 : ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_q0]
  norm_num

