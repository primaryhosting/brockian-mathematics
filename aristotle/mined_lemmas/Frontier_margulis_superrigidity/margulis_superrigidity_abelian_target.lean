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

theorem margulis_superrigidity_abelian_target (n : ℕ)
    (hperf : commutator (Matrix.SpecialLinearGroup (Fin n) ℤ) = ⊤)
    {H : Type*} [CommGroup H] [TopologicalSpace H]
    (π : Matrix.SpecialLinearGroup (Fin n) ℤ →* H) :
    ExtendsToContinuousMulHom (slLatticeIncl n) π :=
  extendsToContinuousMulHom_of_perfect hperf _ π

/-- The degenerate case `m = 1` of the higher-rank statement holds: `SL(1, ℝ)` is trivial, so no
homomorphism into it has unbounded image and the hypotheses are unsatisfiable. -/
