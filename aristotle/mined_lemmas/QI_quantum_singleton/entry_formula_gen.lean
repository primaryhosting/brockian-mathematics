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

lemma entry_formula_gen {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (S : Finset (Fin n)) (asm : (S → Fin q) → B → C → (Fin n → Fin q))
    (hbij : Function.Bijective (fun p : (S → Fin q) × B × C => asm p.1 p.2.1 p.2.2))
    (hres : ∀ a b c, (fun i : S => asm a b c i) = a)
    (hagree : ∀ a a' b b' c c', (∀ i, i ∉ S → asm a b c i = asm a' b' c' i) ↔ (b = b' ∧ c = c'))
    (E : Matrix (Fin n → Fin q) (Fin K) ℂ) (a a' : S → Fin q) (i j : Fin K) :
    (Eᴴ * extendOp S (Matrix.single a a' 1) * E) i j
      = ∑ c, ∑ b, conj (E (asm a b c) i) * E (asm a' b c) j := by
  classical
  have h0 : (Eᴴ * extendOp S (Matrix.single a a' (1:ℂ)) * E) i j
      = ∑ y, ∑ x, (conj (E x i) * extendOp S (Matrix.single a a' (1:ℂ)) x y) * E y j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  have hval : ∀ (p1 r1 : S → Fin q) (p21 r21 : B) (p22 r22 : C),
      extendOp S (Matrix.single a a' (1:ℂ)) (asm p1 p21 p22) (asm r1 r21 r22)
        = if p21 = r21 then (if p22 = r22 then
            (if p1 = a then (if r1 = a' then (1:ℂ) else 0) else 0) else 0) else 0 := by
    intro p1 r1 p21 r21 p22 r22
    simp only [extendOp, hagree, hres, Matrix.single_apply]
    by_cases h : p21 = r21 ∧ p22 = r22
    · rw [if_pos h, if_pos h.1, if_pos h.2]
      by_cases h1 : p1 = a
      · by_cases h2 : r1 = a'
        · simp [h1, h2]
        · simp [h1, h2, Ne.symm h2]
      · simp [h1, Ne.symm h1]
    · rw [if_neg h]
      rcases not_and_or.mp h with h' | h'
      · simp [h']
      · simp [h']
  set e := Equiv.ofBijective _ hbij with he
  have hea : ∀ p : (S → Fin q) × B × C, e p = asm p.1 p.2.1 p.2.2 := fun p => rfl
  rw [h0, ← Equiv.sum_comp e (fun y => ∑ x, (conj (E x i) *
      extendOp S (Matrix.single a a' (1:ℂ)) x y) * E y j)]
  have inner : ∀ r : (S → Fin q) × B × C,
      (∑ x, (conj (E x i) * extendOp S (Matrix.single a a' (1:ℂ)) x (e r)) * E (e r) j)
        = if r.1 = a' then conj (E (asm a r.2.1 r.2.2) i) * E (asm a' r.2.1 r.2.2) j else 0 := by
    intro r
    rw [← Equiv.sum_comp e (fun x => (conj (E x i) *
      extendOp S (Matrix.single a a' (1:ℂ)) x (e r)) * E (e r) j)]
    simp only [hea, hval, Fintype.sum_prod_type]
    simp only [mul_ite, ite_mul, zero_mul, mul_zero]
    by_cases hr : r.1 = a' <;> simp [hr]
  simp only [inner, Fintype.sum_prod_type]
  have hpull : ∀ r1 : S → Fin q,
      (∑ r21 : B, ∑ r22 : C, (if r1 = a' then
          conj (E (asm a r21 r22) i) * E (asm a' r21 r22) j else 0))
        = if r1 = a' then (∑ r21 : B, ∑ r22 : C,
            conj (E (asm a r21 r22) i) * E (asm a' r21 r22) j) else 0 := by
    intro r1; split <;> simp
  rw [Finset.sum_congr rfl (fun r1 _ => hpull r1), Finset.sum_ite_eq' Finset.univ a',
    if_pos (Finset.mem_univ _), Finset.sum_comm]

/-- The code dimension is at most `q ^ (n - |SA| - |SB|)` whenever `SA` and `SB` are two
disjoint sets of at most `d - 1` qudits. -/
