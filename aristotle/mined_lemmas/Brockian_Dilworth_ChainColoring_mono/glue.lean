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

lemma glue {s D U A : Finset α} {n : ℕ} {fD fU : α → ℕ}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hAcard : A.card = n)
    (hAD : A ⊆ D) (hAU : A ⊆ U)
    (hsub : ∀ x ∈ s, x ∈ D ∨ x ∈ U)
    (hD : ∀ x ∈ D, ∃ y ∈ A, x ≤ y) (hU : ∀ x ∈ U, ∃ y ∈ A, y ≤ x)
    (hfD : ChainColoring D n fD) (hfU : ChainColoring U n fU) :
    ∃ f : α → ℕ, ChainColoring s n f := by
  classical
  rcases Finset.eq_empty_or_nonempty A with hAe | ⟨a₀, ha₀⟩
  · -- `A = ∅` forces `s = ∅`
    refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro x hx <;> subst hAe
    · rcases hsub x hx with h | h
      · obtain ⟨y, hy, -⟩ := hD x h; simp at hy
      · obtain ⟨y, hy, -⟩ := hU x h; simp at hy
    · rcases hsub x hx with h | h
      · obtain ⟨y, hy, -⟩ := hD x h; simp at hy
      · obtain ⟨y, hy, -⟩ := hU x h; simp at hy
  · set g : ℕ → α := fun c => if h : ∃ y, y ∈ A ∧ fU y = c then h.choose else a₀ with hgdef
    have hg : ∀ c < n, g c ∈ A ∧ fU (g c) = c := by
      intro c hc
      have hex : ∃ y, y ∈ A ∧ fU y = c := by
        obtain ⟨y, hy, hfy⟩ := hfU.exists_of_lt hAU hA hAcard hc
        exact ⟨y, hy, hfy⟩
      simp only [hgdef, dif_pos hex]
      exact hex.choose_spec
    exact ⟨_, glue_of_matching hA hAD hAU hsub hD hU hfD hfU hg⟩

/-- If `A` is a maximum-size antichain of `s`, then every element of `s` is comparable with some
element of `A`. -/
