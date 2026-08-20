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

lemma exists_clear_row {m : ℕ} (hm : m < n) :
    ∀ (s : Finset (Fin n)), (∀ j ∈ s, m < (j : ℕ)) →
      ∀ B : Matrix.SpecialLinearGroup (Fin n) ℤ, PartialId m (B : Matrix (Fin n) (Fin n) ℤ) →
      (∀ i : Fin n, (B : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0) →
      ∃ h ∈ ESub n,
        PartialId m ((B * h : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) ∧
        (∀ i : Fin n, ((B * h : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0) ∧
        (∀ j ∈ s, ((B * h : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) ⟨m, hm⟩ j = 0) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ B hB hcol
      exact ⟨1, one_mem _, by simpa using hB, by simpa using hcol, by simp⟩
  | insert j s hjs ih =>
      intro hs B hB hcol
      have hs' : ∀ x ∈ s, m < (x : ℕ) := fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hmj : m < (j : ℕ) := hs j (Finset.mem_insert_self j s)
      obtain ⟨h1, hh1, hp1, hcol1, hrow1⟩ := ih hs' B hB hcol
      have hne : (⟨m, hm⟩ : Fin n) ≠ j := by
        intro h
        rw [← h] at hmj
        simp at hmj
      refine ⟨h1 * elemSL ⟨m, hm⟩ j hne
          (-((B * h1 : Matrix.SpecialLinearGroup (Fin n) ℤ) :
            Matrix (Fin n) (Fin n) ℤ) ⟨m, hm⟩ j),
        mul_mem hh1 (elemSL_mem_ESub _ _ _ _), ?_, ?_, ?_⟩
      · rw [← mul_assoc]
        exact partialId_colOp hp1 hne (le_of_eq rfl) (le_of_lt hmj) _
      · rw [← mul_assoc]
        intro i
        rw [mul_elemSL_apply, if_neg hne]
        exact hcol1 i
      · rw [← mul_assoc]
        intro j' hj'
        rw [mul_elemSL_apply]
        rcases Finset.mem_insert.1 hj' with rfl | hjmem
        · rw [if_pos rfl, hcol1 ⟨m, hm⟩]
          simp
        · have hne' : j' ≠ j := by
            rintro rfl
            exact hjs hjmem
          rw [if_neg hne']
          exact hrow1 j' hjmem

/-- **Gaussian elimination.**  Any element of `SL(n, ℤ)` agreeing with the identity on the
first `m` rows and columns is a product of elementary matrices. -/
