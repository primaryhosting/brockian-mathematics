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

lemma partialId_rowOp {m : ℕ} {A : Matrix.SpecialLinearGroup (Fin n) ℤ}
    (hA : PartialId m (A : Matrix (Fin n) (Fin n) ℤ)) {i j : Fin n} (hij : i ≠ j)
    (hi : m ≤ (i : ℕ)) (hj : m ≤ (j : ℕ)) (c : ℤ) :
    PartialId m ((elemSL i j hij c * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
      Matrix (Fin n) (Fin n) ℤ) := by
  intro a b hab
  rw [elemSL_mul_apply]
  by_cases ha : a = i
  · subst ha
    have hb : (b : ℕ) < m := by
      rcases hab with h | h
      · omega
      · exact h
    have h1 : (A : Matrix (Fin n) (Fin n) ℤ) a b = 0 := by
      rw [hA a b (Or.inr hb)]
      have : a ≠ b := fun h => by rw [h] at hi; omega
      simp [this]
    have h2 : (A : Matrix (Fin n) (Fin n) ℤ) j b = 0 := by
      rw [hA j b (Or.inr hb)]
      have : j ≠ b := fun h => by rw [h] at hj; omega
      simp [this]
    have hne : a ≠ b := fun h => by rw [h] at hi; omega
    simp [h1, h2, hne]
  · simp [ha, hA a b hab]

/-- Column operations with both indices outside the first `m` coordinates preserve
`PartialId m`. -/
