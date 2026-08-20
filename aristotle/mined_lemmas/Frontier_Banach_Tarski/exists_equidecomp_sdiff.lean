import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

theorem exists_equidecomp_sdiff {A D : Set X} (ρ : G)
    (hsub : ∀ n : ℕ, (ρ ^ n) • D ⊆ A)
    (hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((ρ ^ n) • D) D) :
    ∃ e : Equidecomp X G, e.source = A \ D ∧ e.target = A := by
  classical
  set U : Set X := ⋃ n : ℕ, (ρ ^ n) • D with hUdef
  set U' : Set X := ⋃ n : ℕ, (ρ ^ (n + 1)) • D with hU'def
  have hUA : U ⊆ A := iUnion_subset hsub
  have hU'U : U' ⊆ U := iUnion_subset fun n => subset_iUnion_of_subset (n + 1) (le_refl _)
  have hU'D : ∀ x ∈ U', x ∉ D := by
    intro x hx hxD
    rw [hU'def, mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact (hdisj (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).notMem_of_mem_left hn hxD
  have hUsplit : ∀ x, x ∈ U → x ∈ D ∨ x ∈ U' := by
    intro x hx
    rw [hUdef, mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    cases n with
    | zero => left; simpa using hn
    | succ m => right; exact mem_iUnion.2 ⟨m, hn⟩
  have hinvU' : ρ⁻¹ • U' = U := by
    rw [hU'def, hUdef, Set.smul_set_iUnion]
    refine iUnion_congr fun n => ?_
    rw [smul_smul, pow_succ', inv_mul_cancel_left]
  refine ⟨mkEquidecomp (fun x => if x ∈ U' then ρ⁻¹ • x else x) (A \ D) A {1, ρ⁻¹} ?_ ?_, rfl, rfl⟩
  · intro a _
    by_cases h : a ∈ U'
    · exact ⟨ρ⁻¹, by simp, by simp [h]⟩
    · exact ⟨1, by simp, by simp [h]⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      by_cases h : x ∈ U'
      · simp only [h, if_true]
        exact hUA (hinvU' ▸ smul_mem_smul_set h)
      · simpa [h] using hx.1
    · intro x hx y hy hxy
      by_cases hx' : x ∈ U' <;> by_cases hy' : y ∈ U' <;>
        simp only [hx', hy', if_true, if_false] at hxy
      · exact MulAction.injective ρ⁻¹ hxy
      · exact absurd (hinvU' ▸ smul_mem_smul_set hx' : ρ⁻¹ • x ∈ U)
          (hxy ▸ fun hc => hy.2 (Or.resolve_right (hUsplit y hc) hy'))
      · exact absurd (hinvU' ▸ smul_mem_smul_set hy' : ρ⁻¹ • y ∈ U)
          (hxy ▸ fun hc => hx.2 (Or.resolve_right (hUsplit x hc) hx'))
      · exact hxy
    · intro y hy
      by_cases h : y ∈ U
      · have hy' : ρ • y ∈ U' := by
          have h2 : ρ • y ∈ ρ • U := smul_mem_smul_set h
          rwa [← hinvU', smul_smul, mul_inv_cancel, one_smul] at h2
        refine ⟨ρ • y, ⟨hUA (hU'U hy'), hU'D _ hy'⟩, ?_⟩
        simp [hy', smul_smul]
      · refine ⟨y, ⟨hy, fun hc => h (subset_iUnion_of_subset 0 (by simp) hc)⟩, ?_⟩
        have hy' : y ∉ U' := fun hc => h (hU'U hc)
        simp [hy']

/-! ### Words starting with a given letter -/

open FreeGroup in
/-- Multiplying a word which does not start with `i` by `i⁻¹` yields a word starting with
`i⁻¹`. -/
