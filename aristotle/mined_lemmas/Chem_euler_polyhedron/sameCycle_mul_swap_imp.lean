import Mathlib

/-!
# Counting the orbits of a permutation, and how a transposition changes the count

This file develops the basic combinatorial tool behind Euler's polyhedron formula:
for a permutation `f` of a finite type, multiplying by a transposition `swap x y`
either *merges* two orbits (if `x` and `y` lie in different orbits of `f`) or
*splits* one orbit into two (if `x` and `y` lie in the same orbit of `f`).
-/

open Equiv Equiv.Perm Function

namespace Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of orbits (cycles, including fixed points) of a permutation of a finite type. -/

lemma sameCycle_mul_swap_imp {f : Perm ι} {x y a b : ι}
    (h : (f * swap x y).SameCycle a b) :
    f.SameCycle a b ∨ (f.SameCycle a x ∧ f.SameCycle y b) ∨
      (f.SameCycle a y ∧ f.SameCycle x b) := by
  set g : Perm ι := f * swap x y with hg
  set T : ι → ι → Prop := fun u v => f.SameCycle u v ∨ (f.SameCycle u x ∧ f.SameCycle y v) ∨
      (f.SameCycle u y ∧ f.SameCycle x v) with hT
  have hsymm : ∀ u v, T u v → T v u := by
    rintro u v (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)
    · exact Or.inr (Or.inl ⟨h2.symm, h1.symm⟩)
  have htrans : ∀ u v w, T u v → T v w → T u w := by
    rintro u v w (h1 | ⟨h1, h1'⟩ | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩ | ⟨h2, h2'⟩)
    · exact Or.inl (h1.trans h2)
    · exact Or.inr (Or.inl ⟨h1.trans h2, h2'⟩)
    · exact Or.inr (Or.inr ⟨h1.trans h2, h2'⟩)
    · exact Or.inr (Or.inl ⟨h1, h1'.trans h2⟩)
    · exact Or.inl (h1.trans ((h2.symm.trans h1'.symm).trans h2'))
    · exact Or.inl (h1.trans h2')
    · exact Or.inr (Or.inr ⟨h1, h1'.trans h2⟩)
    · exact Or.inl (h1.trans h2')
    · exact Or.inl (h1.trans (h2.symm.trans (h1'.symm.trans h2')))
  have hstep : ∀ u, T u (g u) := by
    intro u
    by_cases hux : u = x
    · subst hux
      exact Or.inr (Or.inl ⟨SameCycle.refl _ _, by
        rw [hg]; simp only [Perm.mul_apply, swap_apply_left]; exact ⟨1, by simp⟩⟩)
    by_cases huy : u = y
    · subst huy
      exact Or.inr (Or.inr ⟨SameCycle.refl _ _, by
        rw [hg]; simp only [Perm.mul_apply, swap_apply_right]; exact ⟨1, by simp⟩⟩)
    · refine Or.inl ⟨1, ?_⟩
      rw [hg]
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne hux huy]
  have key : ∀ i : ℤ, T a ((g ^ i) a) := by
    intro i
    induction i using Int.induction_on with
    | zero => exact Or.inl (SameCycle.refl _ _)
    | succ n ih =>
        have hgg : (g ^ ((n : ℤ) + 1)) a = g ((g ^ (n : ℤ)) a) := by
          rw [add_comm, zpow_one_add, Perm.mul_apply]
        rw [hgg]
        exact htrans _ _ _ ih (hstep _)
    | pred n ih =>
        have hgg : (g ^ (-(n : ℤ) - 1)) a = g⁻¹ ((g ^ (-(n : ℤ))) a) := by
          rw [show (-(n : ℤ) - 1) = (-1) + (-(n : ℤ)) by ring, zpow_add, Perm.mul_apply,
            zpow_neg_one]
        rw [hgg]
        refine htrans _ _ _ ih (hsymm _ _ ?_)
        have := hstep (g⁻¹ ((g ^ (-(n : ℤ))) a))
        simpa using this
  obtain ⟨i, hi⟩ := h
  have := key i
  rw [hi] at this
  exact this

omit [Fintype ι] in
/-- Walking along the orbit: as long as the darts `f ^ j y` avoid `x` and `y`, the
permutation `f * swap x y` moves `x` exactly as `f` moves `y`. -/
