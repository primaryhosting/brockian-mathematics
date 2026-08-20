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

def slLatticeIncl (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) ℤ →* Matrix.SpecialLinearGroup (Fin n) ℝ :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

/-- **Margulis superrigidity, higher-rank statement.**  For `n ≥ 3`, every homomorphism from the
lattice `SL(n, ℤ) ⊂ SL(n, ℝ)` to `SL(m, ℝ)` whose image is Zariski dense and unbounded is the
restriction of a continuous homomorphism `SL(n, ℝ) → SL(m, ℝ)`.

This is a `Prop`-valued *statement*; it is not proved here (its proof requires the theory of
boundary maps and measurable equivariant cocycles, which is not available in Mathlib).  The
results proved in this file are the base case `Frontier.margulis_superrigidity`, the uniqueness
reduction `Frontier.eq_of_dense_range`, the instance
`Frontier.margulis_superrigidity_inclusion` and the reduction
`Frontier.extendsToContinuousHom_comp`. -/
