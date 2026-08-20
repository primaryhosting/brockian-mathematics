import Mathlib
/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE FILE HEADER.  Lean 4 requires `import` to be the very first command of a
module, so the requested `/-! ... -/` module docstring is placed immediately after the
single `import Mathlib` line rather than before it; its text is otherwise verbatim.
-/

open scoped BigOperators

namespace Frontier

/-! ## The superrigidity extension property

Margulis superrigidity says, for `G` a semisimple Lie group of real rank `≥ 2`, `Γ ≤ G` an
irreducible lattice and `π : Γ → H` a homomorphism into a simple algebraic group with
unbounded Zariski-dense image, that `π` is the restriction of a *continuous* homomorphism
`G → H`.  The predicate below isolates the conclusion of that theorem: a homomorphism
defined on the lattice extends to a continuous homomorphism of the ambient group.
-/

/-- The conclusion of a superrigidity statement, in additive notation: a homomorphism `π`
defined on a lattice `L` (mapped into the ambient group `G` by the inclusion `ι`) is the
restriction along `ι` of a continuous homomorphism `G → H`. -/

theorem margulisSuperrigidityStatement_one (n : ℕ) : MargulisSuperrigidityStatement n 1 := by
  intro _ π _ hunb
  obtain ⟨A, hA, i, j, hij⟩ := hunb 1
  obtain ⟨γ, rfl⟩ := hA
  have hdet : ((π γ : Matrix.SpecialLinearGroup (Fin 1) ℝ) :
      Matrix (Fin 1) (Fin 1) ℝ).det = 1 := (π γ).2
  rw [Matrix.det_fin_one] at hdet
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi; subst hj
  simp [hdet] at hij

/-- A reduction: the superrigidity conclusion is stable under post-composition with a continuous
homomorphism of the target. -/
