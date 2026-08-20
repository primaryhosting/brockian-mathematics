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

lemma eq_one_of_partialId_succ (A : Matrix.SpecialLinearGroup (Fin n) ℤ) {m : ℕ} (hm : m + 1 = n)
    (h : PartialId m (A : Matrix (Fin n) (Fin n) ℤ)) : A = 1 := by
  have hmn : m < n := by omega
  set i0 : Fin n := ⟨m, hmn⟩ with hi0
  have hcoord : ∀ i : Fin n, i ≠ i0 → (i : ℕ) < m := by
    intro i hi
    have h1 : (i : ℕ) < n := i.isLt
    have h2 : (i : ℕ) ≠ m := by
      intro hc
      exact hi (Fin.ext (by simp [hi0, hc]))
    omega
  have hdiag : (A : Matrix (Fin n) (Fin n) ℤ)
      = Matrix.diagonal fun k => if k = i0 then (A : Matrix (Fin n) (Fin n) ℤ) i0 i0 else 1 := by
    ext p q
    by_cases hp : p = i0
    · by_cases hq : q = i0
      · subst hp; subst hq; simp [Matrix.diagonal_apply_eq]
      · have hqm : (q : ℕ) < m := hcoord q hq
        rw [h p q (Or.inr hqm), Matrix.diagonal_apply_ne _ (by simp [hp, Ne.symm hq])]
        simp [hp, Ne.symm hq]
    · have hpm : (p : ℕ) < m := hcoord p hp
      rw [h p q (Or.inl hpm)]
      by_cases hq : q = p
      · subst hq; simp [Matrix.diagonal_apply_eq, hp]
      · simp [Ne.symm hq]
  have hdet : (A : Matrix (Fin n) (Fin n) ℤ).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal] at hdet
  have hprod : (∏ k : Fin n, if k = i0 then (A : Matrix (Fin n) (Fin n) ℤ) i0 i0 else 1)
      = (A : Matrix (Fin n) (Fin n) ℤ) i0 i0 := by
    simp
  rw [hprod] at hdet
  refine Subtype.ext ?_
  rw [hdiag, hdet]
  simp

/-- To check that the pivot column is a standard basis vector it suffices to check the entries
below the first `m` rows. -/
