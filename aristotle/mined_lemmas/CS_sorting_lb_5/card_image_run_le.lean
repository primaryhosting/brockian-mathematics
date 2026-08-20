import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-! ## Comparison sorts as decision trees

An input to a comparison sort on `n` elements is modelled by a permutation
`σ : Equiv.Perm (Fin n)`, where `σ i` is the rank of the `i`-th input element (so the
input is in "general position": all elements are distinct).  A deterministic
comparison-based sorting algorithm is a binary decision tree: each internal node asks a
comparison "is the `i`-th element ≤ the `j`-th element?" and branches accordingly, and each
leaf outputs a permutation (the algorithm's verdict about the ranking of the input).
-/

/-- A comparison-based decision tree on `n` elements.  Internal nodes compare two positions,
leaves output a permutation. -/
inductive DTree (n : ℕ) where
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n

/-- The output of the algorithm `t` on the input whose ranking is `σ`. -/

theorem card_image_run_le {n : ℕ} :
    ∀ (t : DTree n) (S : Finset (Equiv.Perm (Fin n))) (k : ℕ),
      (∀ σ ∈ S, comps t σ ≤ k) → (S.image (run t)).card ≤ 2 ^ k := by
  intro t
  induction t with
  | leaf p =>
      intro S k _
      refine le_trans (Finset.card_le_one.mpr ?_) (Nat.one_le_two_pow)
      intro a ha b hb
      simp only [Finset.mem_image] at ha hb
      obtain ⟨x, _, hx⟩ := ha
      obtain ⟨y, _, hy⟩ := hb
      simp only [run] at hx hy
      exact hx ▸ hy ▸ rfl
  | node i j l r ihl ihr =>
      intro S k hk
      match k with
      | 0 =>
          -- no comparison is allowed, so `S` must be empty
          have hS : S = ∅ := by
            by_contra h
            obtain ⟨σ, hσ⟩ := Finset.nonempty_iff_ne_empty.mpr h
            have := hk σ hσ
            simp only [comps] at this
            omega
          simp [hS]
      | (m + 1) =>
          set S₁ : Finset (Equiv.Perm (Fin n)) := S.filter (fun σ => σ i ≤ σ j) with hS₁
          set S₂ : Finset (Equiv.Perm (Fin n)) := S.filter (fun σ => ¬ (σ i ≤ σ j)) with hS₂
          have h1 : ∀ σ ∈ S₁, comps l σ ≤ m := by
            intro σ hσ
            rw [hS₁, Finset.mem_filter] at hσ
            have := hk σ hσ.1
            simp only [comps, if_pos hσ.2] at this
            omega
          have h2 : ∀ σ ∈ S₂, comps r σ ≤ m := by
            intro σ hσ
            rw [hS₂, Finset.mem_filter] at hσ
            have := hk σ hσ.1
            simp only [comps, if_neg hσ.2] at this
            omega
          have hsub : S.image (run (DTree.node i j l r)) ⊆
              S₁.image (run l) ∪ S₂.image (run r) := by
            intro a ha
            simp only [Finset.mem_image] at ha
            obtain ⟨σ, hσ, rfl⟩ := ha
            by_cases hc : σ i ≤ σ j
            · refine Finset.mem_union_left _ ?_
              simp only [Finset.mem_image]
              exact ⟨σ, by rw [hS₁, Finset.mem_filter]; exact ⟨hσ, hc⟩, by
                simp only [run, if_pos hc]⟩
            · refine Finset.mem_union_right _ ?_
              simp only [Finset.mem_image]
              exact ⟨σ, by rw [hS₂, Finset.mem_filter]; exact ⟨hσ, hc⟩, by
                simp only [run, if_neg hc]⟩
          calc (S.image (run (DTree.node i j l r))).card
              ≤ (S₁.image (run l) ∪ S₂.image (run r)).card := Finset.card_le_card hsub
            _ ≤ (S₁.image (run l)).card + (S₂.image (run r)).card := Finset.card_union_le _ _
            _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add (ihl S₁ m h1) (ihr S₂ m h2)
            _ = 2 ^ (m + 1) := by ring

/-- A correct comparison sort on `n` elements must, in the worst case, use at least
`⌈log₂ (n!)⌉` comparisons. -/
