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

lemma elemSL_mul_apply (i j : Fin n) (hij : i ≠ j) (c : ℤ)
    (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (a b : Fin n) :
    ((elemSL i j hij c * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
        Matrix (Fin n) (Fin n) ℤ) a b
      = if a = i then (A : Matrix (Fin n) (Fin n) ℤ) i b
          + c * (A : Matrix (Fin n) (Fin n) ℤ) j b
        else (A : Matrix (Fin n) (Fin n) ℤ) a b := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_elemSL]
  by_cases h : a = i
  · subst h; simp
  · simp [h]

/-- Column operation: right multiplication by an elementary matrix adds `c` times column `i` to
column `j`. -/
