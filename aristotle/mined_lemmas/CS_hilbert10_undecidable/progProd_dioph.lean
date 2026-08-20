import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem progProd_dioph {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g)
    (hg : ∀ v, 0 < g v) : DiophFn fun v => progProd (f v) (g v) := by
  set F : (Option (Option α) → ℕ) → ℕ := fun u => f (u ∘ some ∘ some) with hF
  set G : (Option (Option α) → ℕ) → ℕ := fun u => g (u ∘ some ∘ some) with hG
  have dF : DiophFn F := Dioph.reindex_diophFn (some ∘ some) df
  have dG : DiophFn G := Dioph.reindex_diophFn (some ∘ some) dg
  have dZ : DiophFn fun u : Option (Option α) → ℕ => u (some none) := Dioph.proj_dioph _
  have dM : DiophFn fun u : Option (Option α) → ℕ => u none := Dioph.proj_dioph _
  have dMM : DiophFn fun u : Option (Option α) → ℕ => G u * (1 + F u * G u) ^ (F u + 1) + 1 :=
    Dioph.add_dioph (Dioph.mul_dioph dG (Dioph.pow_dioph
      (Dioph.add_dioph (Dioph.const_dioph 1) (Dioph.mul_dioph dF dG))
      (Dioph.add_dioph dF (Dioph.const_dioph 1)))) (Dioph.const_dioph 1)
  have dC1 : Dioph {u : Option (Option α) → ℕ | F u ≤ u none} := Dioph.le_dioph dF dM
  have dC2 : Dioph {u : Option (Option α) → ℕ |
      G u * u none ≡ 1 + F u * G u [MOD (G u * (1 + F u * G u) ^ (F u + 1) + 1)]} :=
    Dioph.modEq_dioph (Dioph.mul_dioph dG dM)
      (Dioph.add_dioph (Dioph.const_dioph 1) (Dioph.mul_dioph dF dG)) dMM
  have dC3 : Dioph {u : Option (Option α) → ℕ | u (some none) =
      (G u ^ F u * ((F u)! * (u none).choose (F u))) %
        (G u * (1 + F u * G u) ^ (F u + 1) + 1)} :=
    Dioph.eq_dioph dZ (Dioph.mod_dioph (Dioph.mul_dioph (Dioph.pow_dioph dG dF)
      (Dioph.mul_dioph (factorial_dioph dF) (choose_dioph dM dF))) dMM)
  refine Dioph.ext (Dioph.ex1_dioph ((dC1.inter dC2).inter dC3)) ?_
  intro w
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hF, hG]
  constructor
  · rintro ⟨m, ⟨⟨h1, h2⟩, h3⟩⟩
    have hcomp : (Option.elim' m w ∘ some ∘ some) = w ∘ some := rfl
    rw [hcomp] at h1 h2 h3
    have hd : m.descFactorial (f (w ∘ some)) = (f (w ∘ some))! * m.choose (f (w ∘ some)) :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    have hpp := progProd_eq (f (w ∘ some)) (g (w ∘ some)) m (hg _) h1 h2
    rw [hd] at hpp
    exact hpp.trans h3.symm
  · intro h
    obtain ⟨m, hm1, hm2⟩ := exists_progProd_witness (f (w ∘ some)) (g (w ∘ some)) (hg _)
    refine ⟨m, ⟨⟨hm1, hm2⟩, ?_⟩⟩
    have hcomp : (Option.elim' m w ∘ some ∘ some) = w ∘ some := rfl
    rw [hcomp]
    have hd : m.descFactorial (f (w ∘ some)) = (f (w ∘ some))! * m.choose (f (w ∘ some)) :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    have hpp := progProd_eq (f (w ∘ some)) (g (w ∘ some)) m (hg _) hm1 hm2
    rw [hd] at hpp
    show w none = _
    rw [← h]
    exact hpp

/-! ### Divisibility helpers for descending factorials -/

/-- If `a` is congruent mod `m` to some `x ≤ u`, then `m` divides the descending factorial
`a (a-1) ⋯ (a-u)`. -/
