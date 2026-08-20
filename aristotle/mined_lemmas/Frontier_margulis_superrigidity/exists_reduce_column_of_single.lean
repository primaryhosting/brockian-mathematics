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

lemma exists_reduce_column_of_single {m : ℕ} (hm : m < n) (hm2 : m + 1 < n)
    (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (hA : PartialId m (A : Matrix (Fin n) (Fin n) ℤ))
    (p : Fin n) (hp : m ≤ (p : ℕ))
    (hzero : ∀ i : Fin n, m ≤ (i : ℕ) → i ≠ p →
      (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = 0) :
    ∃ g ∈ ESub n, PartialId m ((g * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
        Matrix (Fin n) (Fin n) ℤ) ∧
      ∀ i : Fin n, ((g * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
        Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0 := by
  set c : Fin n := ⟨m, hm⟩ with hc
  have hcm : (c : ℕ) = m := rfl
  have hcact : m ≤ (c : ℕ) := le_of_eq hcm.symm
  have hunit : (A : Matrix (Fin n) (Fin n) ℤ) p c = 1 ∨
      (A : Matrix (Fin n) (Fin n) ℤ) p c = -1 := by
    rw [← Int.isUnit_iff]
    refine column_isUnit_of_dvd hm A hA _ fun i hi => ?_
    by_cases hip : i = p
    · rw [hip]
    · rw [hzero i hi hip]
      exact dvd_zero _
  have hsq : (A : Matrix (Fin n) (Fin n) ℤ) p c * (A : Matrix (Fin n) (Fin n) ℤ) p c = 1 := by
    rcases hunit with h | h <;> rw [h] <;> norm_num
  by_cases hpc : p = c
  · subst hpc
    rcases hunit with h1 | h1
    · refine ⟨1, one_mem _, ?_, ?_⟩
      · simpa using hA
      · refine column_eq_of_active hm _ (by simpa using hA) fun i hi => ?_
        by_cases hic : i = c
        · rw [hic, if_pos rfl]
          simpa using h1
        · rw [if_neg hic]
          simpa using hzero i hi hic
    · set j : Fin n := ⟨m + 1, hm2⟩ with hj
      have hjact : m ≤ (j : ℕ) := by simp [hj]
      have hjc : j ≠ c := by
        intro h
        have h2 : (j : ℕ) = (c : ℕ) := by rw [h]
        simp [hj, hcm] at h2
      have hcj : c ≠ j := Ne.symm hjc
      have hAjc : (A : Matrix (Fin n) (Fin n) ℤ) j c = 0 := hzero j hjact hjc
      refine ⟨elemSL j c hjc 1 * (elemSL c j hcj (-2) * elemSL j c hjc 1), ?_, ?_, ?_⟩
      · exact mul_mem (elemSL_mem_ESub _ _ _ _)
          (mul_mem (elemSL_mem_ESub _ _ _ _) (elemSL_mem_ESub _ _ _ _))
      · rw [mul_assoc, mul_assoc]
        exact partialId_rowOp (partialId_rowOp (partialId_rowOp hA hjc hjact hcact 1)
          hcj hcact hjact (-2)) hjc hjact hcact 1
      · rw [mul_assoc, mul_assoc]
        refine column_eq_of_active hm _ (partialId_rowOp (partialId_rowOp
          (partialId_rowOp hA hjc hjact hcact 1) hcj hcact hjact (-2)) hjc hjact hcact 1)
          fun i hi => ?_
        simp only [elemSL_mul_apply, ← hc]
        by_cases hij : i = j
        · simp [hij, hjc, hcj, hAjc, h1]
        · by_cases hic : i = c
          · simp [hic, hcj, hAjc, h1]
          · simp [hij, hic, hzero i hi hic]
  · have hcp : c ≠ p := fun h => hpc h.symm
    have hpc' : p ≠ c := hpc
    have hAcc : (A : Matrix (Fin n) (Fin n) ℤ) c c = 0 := hzero c hcact hcp
    refine ⟨elemSL p c hpc' (-(A : Matrix (Fin n) (Fin n) ℤ) p c) *
      elemSL c p hcp ((A : Matrix (Fin n) (Fin n) ℤ) p c), ?_, ?_, ?_⟩
    · exact mul_mem (elemSL_mem_ESub _ _ _ _) (elemSL_mem_ESub _ _ _ _)
    · rw [mul_assoc]
      exact partialId_rowOp (partialId_rowOp hA hcp hcact hp _) hpc' hp hcact _
    · rw [mul_assoc]
      refine column_eq_of_active hm _ (partialId_rowOp (partialId_rowOp hA hcp hcact hp _)
        hpc' hp hcact _) fun i hi => ?_
      simp only [elemSL_mul_apply, ← hc]
      by_cases hip : i = p
      · simp [hip, hpc', hAcc, hsq]
      · by_cases hic : i = c
        · simp [hic, hcp, hAcc, hsq]
        · simp [hip, hic, hzero i hi hip]

/-- The sum of the absolute values of the pivot column below the first `m` rows. -/
