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

lemma column_eq_of_active {m : ℕ} (hm : m < n) (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (hA : PartialId m (A : Matrix (Fin n) (Fin n) ℤ))
    (h : ∀ i : Fin n, m ≤ (i : ℕ) →
      (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0) :
    ∀ i : Fin n, (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0 := by
  intro i
  by_cases hi : m ≤ (i : ℕ)
  · exact h i hi
  · push_neg at hi
    exact hA i ⟨m, hm⟩ (Or.inl hi)

/-- Terminal step of the column reduction: if at most one entry of the pivot column is nonzero,
elementary row operations turn the pivot column into a standard basis vector. -/
