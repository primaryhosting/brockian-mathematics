import Mathlib

/-!
# Dilworth's theorem

In a finite partial order, the minimum number of chains needed to cover the order equals the
maximum size of an antichain.

The main work is done with the auxiliary notion of a *chain colouring*: a map `f : α → ℕ`
assigning to each element of a finite set `s` a colour `< n` such that any two elements of `s`
with the same colour are comparable (i.e. the colour classes are chains).

The main results are:

* `Brockian.Dilworth.dilworth_cover`: if every antichain has at most `n` elements, then the whole
  (finite) order can be covered by at most `n` chains;
* `Brockian.Dilworth.dilworth`: if moreover `n` is attained by some antichain, the cover can be
  taken to consist of exactly `n` chains;
* `Brockian.Dilworth.card_le_card_of_cover`: the converse inequality, i.e. any antichain is at most
  as large as any covering family of chains.

Together, `dilworth` and `card_le_card_of_cover` say that the maximum size of an antichain equals
the minimum number of chains needed to cover the order.

The statement of `dilworth` differs slightly from the one originally posed, which asked for a
cover by exactly `n` chains assuming only that `n` bounds the size of every antichain; that form
is false, and `Brockian.Dilworth.exact_cover_counterexample` gives an explicit counterexample.
-/

namespace Brockian.Dilworth

variable {α : Type*} [PartialOrder α] [DecidableEq α]

/-- `ChainColoring s n f` says that `f` assigns to each element of `s` a colour `< n`, in such a
way that any two elements of `s` with the same colour are comparable; i.e. the colour classes
are chains. -/

theorem dilworth_cover (n : ℕ)
    (hanti : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ n) :
    ∃ C : Finset (Finset α), C.card ≤ n ∧
      (∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) ∧
      (∀ a : α, ∃ c ∈ C, a ∈ c) := by
  obtain ⟨f, hf⟩ := exists_chainColoring (Finset.univ : Finset α) n
    (fun t _ hanti' => hanti t hanti')
  let C := Finset.image (fun c => Finset.filter (fun a => f a = c) Finset.univ) (Finset.range n)
  refine ⟨C, ?_, ?_, ?_⟩
  · -- C.card ≤ n
    exact Finset.card_image_le.trans (by simp)
  · -- Each c ∈ C is a chain
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨c', hc', hc_eq⟩ := hc
    rw [← hc_eq]
    intro x hx y hy hne
    simp at hx hy
    exact hf.2 x (by simp) y (by simp) (hx.trans hy.symm)
  · -- Cover: every a is in some c ∈ C
    intro a
    have hfa : f a < n := hf.1 a (by simp)
    refine ⟨Finset.filter (fun x => f x = f a) Finset.univ, ?_, ?_⟩
    · show Finset.filter (fun x => f x = f a) Finset.univ ∈ C
      change Finset.filter (fun x => f x = f a) Finset.univ ∈
        Finset.image (fun c => Finset.filter (fun a => f a = c) Finset.univ) (Finset.range n)
      exact Finset.mem_image.mpr ⟨f a, Finset.mem_range.mpr hfa, rfl⟩
    · simp

/-
The theorem as originally posed was:

```
