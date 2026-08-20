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

lemma step_case_one {s : Finset α} {a b : α} {n : ℕ} (hba : b ≤ a) (hn : 1 ≤ n)
    {f' : α → ℕ} (hf' : ChainColoring (s \ {a, b}) (n - 1) f') :
    ∃ f : α → ℕ, ChainColoring s n f := by
  let f : α → ℕ := fun x => if x = a ∨ x = b then n - 1 else f' x
  refine ⟨f, ?_, ?_⟩
  · -- f x < n for all x ∈ s
    intro x hx
    by_cases hxa : x = a ∨ x = b
    · simp [f, hxa]
      omega
    · simp [f, hxa]
      have hxmem : x ∈ s \ {a, b} := Finset.mem_sdiff.mpr ⟨hx, fun h => hxa (by simpa using Finset.mem_insert.mp h)⟩
      exact lt_trans (hf'.1 x hxmem) (Nat.sub_lt (by omega) (by omega))
  · -- comparability
    intro x hx y hy hxy
    by_cases hxa : x = a ∨ x = b
    · -- x ∈ {a, b}, so f x = n - 1
      have hfx : f x = n - 1 := by simp [f, hxa]
      rw [hfx] at hxy
      by_cases hyb : y = a ∨ y = b
      · -- y ∈ {a, b}, so both in {a, b}
        simp [f, hyb] at hxy
        rcases hxa with rfl | rfl <;> rcases hyb with rfl | rfl <;> simp_all
      · -- y ∉ {a, b}, so y ∈ s \ {a, b}
        have hyin : y ∈ s \ {a, b} := Finset.mem_sdiff.mpr ⟨hy, fun h => hyb (by simpa using Finset.mem_insert.mp h)⟩
        have hf'y : f y = f' y := by simp [f, hyb]
        rw [hf'y] at hxy
        have := hf'.1 y hyin
        omega
    · -- x ∉ {a, b}, so x ∈ s \ {a, b}
      have hxin : x ∈ s \ {a, b} := Finset.mem_sdiff.mpr ⟨hx, fun h => hxa (by simpa using Finset.mem_insert.mp h)⟩
      by_cases hyb : y = a ∨ y = b
      · -- y ∈ {a, b}
        have hfy : f y = n - 1 := by simp [f, hyb]
        have hfx : f x = f' x := by simp [f, hxa]
        rw [hfx, hfy] at hxy
        have := hf'.1 x hxin
        omega
      · -- y ∉ {a, b}, so y ∈ s \ {a, b}
        have hyin : y ∈ s \ {a, b} := Finset.mem_sdiff.mpr ⟨hy, fun h => hyb (by simpa using Finset.mem_insert.mp h)⟩
        have hfx : f x = f' x := by simp [f, hxa]
        have hfy : f y = f' y := by simp [f, hyb]
        rw [hfx, hfy] at hxy
        exact hf'.2 x hxin y hyin hxy

/-- Second case of the inductive step: `s` contains an antichain `A` of maximum size `n` avoiding
the maximal element `a` and the minimal element `b`.  Splitting `s` into the elements below `A`
and the elements above `A` and applying the inductive hypothesis to both halves, the two
colourings can be glued along `A`. -/
