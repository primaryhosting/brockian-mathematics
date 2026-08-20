import Mathlib

/-!
Rank tools and the core decoupling lemma behind the quantum Singleton bound.
-/

open Matrix Module
open scoped ComplexOrder

namespace QI

variable {X Y Z R : Type*}

section RankTools

/-- Vectors on `Z × X` all of whose `Z`-slices lie in `W`. -/

lemma extendOp_empty (O : Matrix ((∅ : Finset (Fin n)) → Fin q) ((∅ : Finset (Fin n)) → Fin q) ℂ)
    (e : (∅ : Finset (Fin n)) → Fin q) :
    extendOp (∅ : Finset (Fin n)) O = (O e e) • (1 : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ) := by
  classical
  ext x y
  have hsub : ∀ g h : (∅ : Finset (Fin n)) → Fin q, g = h := by
    intro g h; funext i; exact (Finset.notMem_empty _ i.2).elim
  by_cases hxy : x = y
  · subst hxy
    simp only [extendOp, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [if_pos (by simp), hsub (fun i : (∅ : Finset (Fin n)) => x i) e]
  · have hne : ¬ (∀ i, i ∉ (∅ : Finset (Fin n)) → x i = y i) := by
      intro h; exact hxy (funext fun i => h i (Finset.notMem_empty i))
    simp only [extendOp, if_neg hne, Matrix.smul_apply, Matrix.one_apply_ne hxy, smul_eq_mul,
      mul_zero]

/-- The unencoded encoding map on `n` qudits. -/
