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

lemma step_case_two {s A : Finset α} {n : ℕ} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hamax : ∀ x ∈ s, a ≤ x → x = a) (hbmin : ∀ x ∈ s, x ≤ b → x = b)
    (haA : a ∉ A) (hbA : b ∉ A)
    (hAs : A ⊆ s) (hAanti : IsAntichain (· ≤ ·) (A : Set α)) (hAcard : A.card = n)
    (h : ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ n)
    (IH : ∀ t : Finset α, t.card < s.card → ∀ m : ℕ,
      (∀ u ⊆ t, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ m) → ∃ f : α → ℕ, ChainColoring t m f) :
    ∃ f : α → ℕ, ChainColoring s n f := by
  classical
  -- Define D = {x ∈ s | ∃ y ∈ A, x ≤ y} and U = {x ∈ s | ∃ y ∈ A, y ≤ x}
  let pD : α → Prop := fun x => ∃ y ∈ A, x ≤ y
  let pU : α → Prop := fun x => ∃ y ∈ A, y ≤ x
  let D := Finset.filter (fun x => pD x) s
  let U := Finset.filter (fun x => pU x) s
  -- Show every element of s is in D or U
  have hsub : ∀ x ∈ s, x ∈ D ∨ x ∈ U := by
    intro x hx
    rcases mem_up_or_down hAs hAanti hAcard h hx with ⟨y, hy, hxy⟩ | ⟨y, hy, hyx⟩
    · left; exact Finset.mem_filter.mpr ⟨hx, y, hy, hxy⟩
    · right; exact Finset.mem_filter.mpr ⟨hx, y, hy, hyx⟩
  -- Show A ⊆ D and A ⊆ U
  have hAD : A ⊆ D := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hAs hx, x, hx, le_refl x⟩
  have hAU : A ⊆ U := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hAs hx, x, hx, le_refl x⟩
  -- Show the covering conditions
  have hD : ∀ x ∈ D, ∃ y ∈ A, x ≤ y := fun x hx => (Finset.mem_filter.mp hx).2
  have hU : ∀ x ∈ U, ∃ y ∈ A, y ≤ x := fun x hx => (Finset.mem_filter.mp hx).2
  -- Show D is a proper subset of s (a ∉ D because a is maximal and a ∉ A)
  have ha_notin_D : a ∉ D := by
    intro haD
    obtain ⟨y, hyA, hay⟩ := hD a haD
    have : y = a := hamax y (hAs hyA) hay
    exact haA (this ▸ hyA)
  have hDsub : D ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, by
    intro heq
    exact ha_notin_D (heq ▸ ha)⟩
  have hD_card : D.card < s.card := Finset.card_lt_card hDsub
  -- Similarly U is a proper subset of s (b ∉ U because b is minimal and b ∉ A)
  have hb_notin_U : b ∉ U := by
    intro hbU
    obtain ⟨y, hyA, hyb⟩ := hU b hbU
    have : y = b := hbmin y (hAs hyA) hyb
    exact hbA (this ▸ hyA)
  have hUsub : U ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, by
    intro heq
    exact hb_notin_U (heq ▸ hb)⟩
  have hU_card : U.card < s.card := Finset.card_lt_card hUsub
  -- Apply IH to D and U
  have hD_bound : ∀ u ⊆ D, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ n := by
    intro u hu hanti
    exact h u (hu.trans (Finset.filter_subset _ _)) hanti
  have hU_bound : ∀ u ⊆ U, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ n := by
    intro u hu hanti
    exact h u (hu.trans (Finset.filter_subset _ _)) hanti
  obtain ⟨fD, hfD⟩ := IH D hD_card n hD_bound
  obtain ⟨fU, hfU⟩ := IH U hU_card n hU_bound
  -- Use glue to combine
  exact glue hAanti hAcard hAD hAU hsub hD hU hfD hfU

/-- The inductive step in the proof of Dilworth's theorem. -/
