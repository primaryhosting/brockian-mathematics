/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix Complex
open scoped Kronecker

/-- The Pauli `X` matrix. -/

theorem no_local_hidden_variables (x y : Fin 3 → ℤ)
    (hx : ∀ i, x i = 1 ∨ x i = -1) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    ¬ (x 0 * y 1 * y 2 = -1 ∧ y 0 * x 1 * y 2 = -1 ∧ y 0 * y 1 * x 2 = -1 ∧
       x 0 * x 1 * x 2 = 1) := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases hx 0 with hx0 | hx0 <;> rcases hx 1 with hx1 | hx1 <;> rcases hx 2 with hx2 | hx2 <;>
    rcases hy 0 with hy0 | hy0 <;> rcases hy 1 with hy1 | hy1 <;> rcases hy 2 with hy2 | hy2 <;>
      rw [hx0, hx1, hx2] at h4 <;>
      simp_all

/-- **GHZ nonlocality (Mermin's paradox).**

The GHZ state `|000⟩ + |111⟩` is a simultaneous eigenvector of the four observables
`X⊗Y⊗Y`, `Y⊗X⊗Y`, `Y⊗Y⊗X` (eigenvalue `-1`) and `X⊗X⊗X` (eigenvalue `+1`), so quantum
mechanics predicts these four products of measurement outcomes with certainty; yet no local
hidden-variable model, i.e. no predetermined `±1` outcomes `x i`, `y i` for the local `X` and
`Y` measurements, can reproduce all four predictions. -/
