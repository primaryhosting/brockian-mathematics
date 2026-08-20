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

theorem commutator_specialLinearGroup_int_eq_top {n : ℕ} (hn : 3 ≤ n) :
    commutator (Matrix.SpecialLinearGroup (Fin n) ℤ) = ⊤ :=
  commutator_eq_top_of_elemSet_generates hn (elemSet_closure_eq_top n)

/-- **Margulis superrigidity for `SL(n, ℤ) ⊂ SL(n, ℝ)`, abelian targets, unconditional.**
For `n ≥ 3` every homomorphism of the lattice `SL(n, ℤ)` into an abelian topological group is
the restriction of a continuous homomorphism of the ambient group `SL(n, ℝ)`. -/
