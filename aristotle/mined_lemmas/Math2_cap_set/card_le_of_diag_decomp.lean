import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/

theorem card_le_of_diag_decomp {I₁ I₂ I₃ : Type*} [Fintype I₁] [Fintype I₂] [Fintype I₃]
    (f₁ : I₁ → X → F) (g₁ : I₁ → X → X → F)
    (f₂ : I₂ → X → F) (g₂ : I₂ → X → X → F)
    (f₃ : I₃ → X → F) (g₃ : I₃ → X → X → F)
    (h : ∀ x y z : X, (if x = y ∧ y = z then (1 : F) else 0)
      = (∑ i, f₁ i x * g₁ i y z) + (∑ i, f₂ i y * g₂ i x z) + (∑ i, f₃ i z * g₃ i x y)) :
    Fintype.card X ≤ Fintype.card I₁ + Fintype.card I₂ + Fintype.card I₃ := by
  classical
  -- Step 1: kill the first family of slices by passing to the kernel of `u ↦ (∑ₓ u x f₁ i x)ᵢ`.
  let L : (X → F) →ₗ[F] (I₁ → F) :=
    { toFun := fun u i => ∑ x, u x * f₁ i x
      map_add' := by intro a b; funext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a b; funext i; simp [Finset.mul_sum, mul_assoc] }
  have hcard : Fintype.card X ≤ Fintype.card I₁ + Module.finrank F (LinearMap.ker L) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    have h2 : Module.finrank F (LinearMap.range L) ≤ Fintype.card I₁ := by
      have h := Submodule.finrank_le (LinearMap.range L)
      simpa using h
    have h3 : Module.finrank F (X → F) = Fintype.card X := by simp
    omega
  obtain ⟨S, u, huW, huS, hSge⟩ := exists_large_support (LinearMap.ker L)
  have hu0 : ∀ i, ∑ x, u x * f₁ i x = 0 := by
    intro i
    have h := LinearMap.mem_ker.mp huW
    exact congrFun h i
  -- Step 2: the resulting matrix is diagonal with `S.card` nonzero entries,
  -- but has rank at most `card I₂ + card I₃`.
  set A : X → X → F := fun y z => ∑ x, u x * (if x = y ∧ y = z then (1 : F) else 0) with hA
  have claim1 : ∀ y z, A y z = if y = z then u y else 0 := by
    intro y z
    by_cases hyz : y = z
    · subst hyz; simp [hA]
    · simp [hA, hyz]
  have claim2 : ∀ y z, A y z
      = (∑ i, f₂ i y * (∑ x, u x * g₂ i x z)) + (∑ i, (∑ x, u x * g₃ i x y) * f₃ i z) := by
    intro y z
    have : A y z = ∑ x, u x * ((∑ i, f₁ i x * g₁ i y z) + (∑ i, f₂ i y * g₂ i x z)
        + (∑ i, f₃ i z * g₃ i x y)) := by
      rw [hA]
      exact Finset.sum_congr rfl fun x _ => by rw [← h x y z]
    rw [this]
    have e1 : ∑ x, u x * (∑ i, f₁ i x * g₁ i y z) = 0 := by
      have step : ∀ x : X, u x * (∑ i, f₁ i x * g₁ i y z) = ∑ i, u x * f₁ i x * g₁ i y z := by
        intro x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.sum_mul, hu0 i, zero_mul]
    have e2 : ∑ x, u x * (∑ i, f₂ i y * g₂ i x z) = ∑ i, f₂ i y * (∑ x, u x * g₂ i x z) := by
      have step : ∀ x : X, u x * (∑ i, f₂ i y * g₂ i x z) = ∑ i, f₂ i y * (u x * g₂ i x z) := by
        intro x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    have e3 : ∑ x, u x * (∑ i, f₃ i z * g₃ i x y) = ∑ i, (∑ x, u x * g₃ i x y) * f₃ i z := by
      have step : ∀ x : X, u x * (∑ i, f₃ i z * g₃ i x y) = ∑ i, (u x * g₃ i x y) * f₃ i z := by
        intro x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    simp only [mul_add, Finset.sum_add_distrib, e1, e2, e3, zero_add]
  -- the family of rows indexed by `S` is linearly independent
  have hLI : LinearIndependent F (fun y : S => A (y : X)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc y
    have hy := congrFun hc (y : X)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hy
    rw [Finset.sum_eq_single y] at hy
    · rw [claim1, if_pos rfl] at hy
      rcases mul_eq_zero.mp hy with h' | h'
      · exact h'
      · exact absurd h' (huS (y : X) y.2)
    · intro b _ hb
      rw [claim1]
      have : (b : X) ≠ (y : X) := fun hbe => hb (Subtype.ext hbe)
      simp [this]
    · intro hy'
      exact absurd (Finset.mem_univ y) hy'
  -- but every row lies in the span of `card I₂ + card I₃` vectors
  let V : I₂ ⊕ I₃ → (X → F) := fun i => match i with
    | Sum.inl i => fun z => ∑ x, u x * g₂ i x z
    | Sum.inr i => fun z => f₃ i z
  have hspan : ∀ y : S, A (y : X) ∈ Submodule.span F (Set.range V) := by
    intro y
    have : A (y : X) = (∑ i : I₂, f₂ i (y : X) • V (Sum.inl i))
        + (∑ i : I₃, (∑ x, u x * g₃ i x (y : X)) • V (Sum.inr i)) := by
      funext z
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, V]
      exact claim2 (y : X) z
    rw [this]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inr i, rfl⟩
  letI : Fintype (Set.range V) := Set.Finite.fintype (Set.finite_range V)
  have hle : (Cardinal.mk S) ≤ (Fintype.card (Set.range V) : Cardinal) :=
    linearIndependent_le_span' _ hLI (Set.range V) (by
      rintro _ ⟨y, rfl⟩
      exact hspan y)
  have hle' : S.card ≤ Fintype.card I₂ + Fintype.card I₃ := by
    have h1 : Fintype.card S ≤ Fintype.card (Set.range V) := by
      simpa [Cardinal.mk_fintype] using hle
    have h2 : Fintype.card (Set.range V) ≤ Fintype.card (I₂ ⊕ I₃) := Fintype.card_range_le V
    simp only [Fintype.card_coe, Fintype.card_sum] at h1 h2 ⊢
    omega
  omega

end CapSetAux

import RequestProject.CapBound

/-!
# Counting low-degree exponent vectors

A Chernoff-type estimate: the number of vectors in `{0,1,2}ⁿ` whose coordinate sum is at
most `2n/3` is exponentially smaller than `3ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

