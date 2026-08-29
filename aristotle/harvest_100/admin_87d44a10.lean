import Mathlib
import RequestProject.Frontier

/-!
# Gale–Stewart for open games: the topological form

`RequestProject.Frontier` proves the Gale–Stewart theorem `Frontier.Gale_Stewart_open` with the
combinatorial formulation of openness (`Frontier.IsOpenPayoff`).  Here we check that this
hypothesis is exactly openness of the payoff set in the product topology on `ℕ → A` where `A`
carries the discrete topology, and record the resulting topological statement
`Frontier.Gale_Stewart_open_topological`.

(Discreteness of `A` is only needed for the converse implication
`Frontier.isOpen_of_isOpenPayoff`; openness for an arbitrary topology on `A` already implies the
combinatorial condition, hence determinacy.)
-/

namespace Frontier

universe u

variable {A : Type u} [TopologicalSpace A]

/-- An open set of the product topology on `ℕ → A` is an open payoff set. -/
theorem isOpenPayoff_of_isOpen {W : Set (ℕ → A)} (hW : IsOpen W) :
    IsOpenPayoff (fun x => x ∈ W) := by
  intro x hx
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hW x hx
  refine ⟨(I.sup id) + 1, fun y hy => hsub ?_⟩
  intro i hi
  have : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [hy i (by omega)]
  exact (hu i hi).2

/-- Conversely, for discrete `A` an open payoff set is open in the product topology. -/
theorem isOpen_of_isOpenPayoff [DiscreteTopology A] {W : Set (ℕ → A)}
    (hW : IsOpenPayoff (fun x => x ∈ W)) : IsOpen W := by
  rw [isOpen_pi_iff]
  intro x hx
  obtain ⟨n, hn⟩ := hW x hx
  refine ⟨Finset.range n, fun i => {x i}, fun i _ => ⟨isOpen_discrete _, rfl⟩, fun y hy => ?_⟩
  exact hn y fun i hi => hy i (Finset.mem_range.mpr hi)

/-- **Gale–Stewart theorem, topological form.**  If the payoff set `W` is open in the product
topology on `ℕ → A` (for `A` discrete, this is the usual topology on the space of plays), then
the game is determined. -/
theorem Gale_Stewart_open_topological [Inhabited A] (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : Strategy A, ∀ τ : Strategy A, play [] σ τ ∈ W) ∨
    (∃ τ : Strategy A, ∀ σ : Strategy A, play [] σ τ ∉ W) :=
  Gale_Stewart_open (fun x => x ∈ W) (isOpenPayoff_of_isOpen hW)

end Frontier

#print axioms Frontier.Gale_Stewart_open
#print axioms Frontier.Gale_Stewart_open_topological

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Gale–Stewart theorem for open games

We formalise the infinite two-player game on a nonempty type `A` of moves with payoff set
`W : (Nat → A) → Prop`.  Player I plays the moves with even index, Player II the moves with odd
index, and Player I wins a play `x : Nat → A` iff `W x`.

A *strategy* is a function `List A → A` assigning a move to every finite position (the list of
moves played so far, in chronological order).  Given a starting position `p` and strategies
`σ` (for I) and `τ` (for II), `Frontier.pos p σ τ k` is the position after `k` further moves and
`Frontier.play p σ τ : Nat → A` is the resulting infinite play.

`Frontier.IsOpenPayoff W` says that `W` is open in the product topology on `Nat → A` where `A`
carries the discrete topology: every winning play has a finite initial segment all of whose
extensions are winning.  (That this is literally equivalent to `IsOpen W` for the Mathlib product
topology is proved in `RequestProject.FrontierTopology`.)

The Gale–Stewart theorem `Frontier.Gale_Stewart_open` then states that an open game is
determined: one of the two players has a winning strategy.

This file is deliberately independent of Mathlib, so that the required header comment can be the
very first thing in the file.
-/

namespace Frontier

universe u

/-- A strategy: a move for every finite position (list of moves played so far). -/
abbrev Strategy (A : Type u) := List A → A

attribute [local instance 0] Classical.propDecidable

variable {A : Type u} [Inhabited A]

/-- `pos p σ τ k` is the position reached from the position `p` after `k` further moves, when
Player I follows `σ` and Player II follows `τ`.  Player I moves at positions of even length. -/
def pos (p : List A) (σ τ : Strategy A) : Nat → List A
  | 0 => p
  | k + 1 => (pos p σ τ k) ++
      [if (pos p σ τ k).length % 2 = 0 then σ (pos p σ τ k) else τ (pos p σ τ k)]

/-- The infinite play obtained from position `p` when I follows `σ` and II follows `τ`. -/
def play (p : List A) (σ τ : Strategy A) (n : Nat) : A := (pos p σ τ (n + 1)).getD n default

omit [Inhabited A] in
@[simp] theorem pos_zero (p : List A) (σ τ : Strategy A) : pos p σ τ 0 = p := rfl

omit [Inhabited A] in
theorem pos_succ (p : List A) (σ τ : Strategy A) (k : Nat) :
    pos p σ τ (k + 1) = (pos p σ τ k) ++
      [if (pos p σ τ k).length % 2 = 0 then σ (pos p σ τ k) else τ (pos p σ τ k)] := rfl

omit [Inhabited A] in
@[simp] theorem pos_length (p : List A) (σ τ : Strategy A) (k : Nat) :
    (pos p σ τ k).length = p.length + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pos_succ]; simp [ih]; omega

omit [Inhabited A] in
theorem pos_prefix_succ (p : List A) (σ τ : Strategy A) (k : Nat) :
    pos p σ τ k <+: pos p σ τ (k + 1) := by
  rw [pos_succ]; exact List.prefix_append _ _

omit [Inhabited A] in
theorem pos_prefix_mono (p : List A) (σ τ : Strategy A) {k l : Nat} (h : k ≤ l) :
    pos p σ τ k <+: pos p σ τ l := by
  induction l with
  | zero =>
    have : k = 0 := Nat.le_zero.mp h
    subst this; exact List.prefix_rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h' | h'
    · exact (ih (by omega)).trans (pos_prefix_succ p σ τ l)
    · have : k = l + 1 := by omega
      subst this; exact List.prefix_rfl

omit [Inhabited A] in
theorem prefix_pos (p : List A) (σ τ : Strategy A) (k : Nat) : p <+: pos p σ τ k := by
  simpa using pos_prefix_mono p σ τ (Nat.zero_le k)

theorem getD_of_prefix {l₁ l₂ : List A} (h : l₁ <+: l₂) {n : Nat} (hn : n < l₁.length) :
    l₂.getD n default = l₁.getD n default := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hn]

/-- The play agrees with any sufficiently long position along the play. -/
theorem play_eq_getD (p : List A) (σ τ : Strategy A) {n k : Nat} (h : n < p.length + k) :
    play p σ τ n = (pos p σ τ k).getD n default := by
  rcases Nat.le_total k (n + 1) with hk | hk
  · rw [play, getD_of_prefix (pos_prefix_mono p σ τ hk) (by simp; omega)]
  · rw [play, getD_of_prefix (pos_prefix_mono p σ τ hk) (by simp; omega)]

theorem play_eq_of_lt (p : List A) (σ τ : Strategy A) {n : Nat} (h : n < p.length) :
    play p σ τ n = p.getD n default := by
  rw [play_eq_getD p σ τ (k := 0) (by omega)]; simp

omit [Inhabited A] in
/-- Positions reached from `p` only depend on the strategies at positions extending `p`. -/
theorem pos_congr {p : List A} {σ σ' τ τ' : Strategy A}
    (hσ : ∀ q, p <+: q → σ q = σ' q) (hτ : ∀ q, p <+: q → τ q = τ' q) (k : Nat) :
    pos p σ τ k = pos p σ' τ' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pos_succ, pos_succ, ih, hσ _ (by rw [← ih]; exact prefix_pos p σ τ k),
      hτ _ (by rw [← ih]; exact prefix_pos p σ τ k)]

omit [Inhabited A] in
/-- Playing from `p` for `j + k` moves is the same as playing from `pos p σ τ j` for `k` moves. -/
theorem pos_add (p : List A) (σ τ : Strategy A) (j k : Nat) :
    pos p σ τ (j + k) = pos (pos p σ τ j) σ τ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, pos_succ, pos_succ, ih]

/-- If the run from `p` after `j` moves coincides with the run from `p'`, the plays agree. -/
theorem play_eq_of_shift {p p' : List A} {σ σ' τ τ' : Strategy A} {j : Nat}
    (h : ∀ k, pos p σ τ (j + k) = pos p' σ' τ' k) (hlen : p'.length = p.length + j) :
    play p σ τ = play p' σ' τ' := by
  funext n
  have h1 : play p σ τ n = (pos p σ τ (j + (n + 1))).getD n default :=
    play_eq_getD p σ τ (by omega)
  have h2 : play p' σ' τ' n = (pos p' σ' τ' (n + 1)).getD n default :=
    play_eq_getD p' σ' τ' (by omega)
  rw [h1, h2, h]

/-- `W` is open in the product topology on `Nat → A` with `A` discrete: every play in `W` has a
finite initial segment all of whose extensions lie in `W`. -/
def IsOpenPayoff (W : (Nat → A) → Prop) : Prop :=
  ∀ x, W x → ∃ n, ∀ y, (∀ i, i < n → y i = x i) → W y

/-- Player I has a winning strategy from the position `p`. -/
def IWins (W : (Nat → A) → Prop) (p : List A) : Prop :=
  ∃ σ : Strategy A, ∀ τ : Strategy A, W (play p σ τ)

/-- If Player I is to move at `p` and some move leads to a position winning for Player I, then
`p` is winning for Player I. -/
theorem IWins_of_move {W : (Nat → A) → Prop} {p : List A} (hp : p.length % 2 = 0) {a : A}
    (h : IWins W (p ++ [a])) : IWins W p := by
  obtain ⟨σ', hσ'⟩ := h
  let σ : Strategy A := fun q => if q = p then a else σ' q
  have hσdef : ∀ q, σ q = if q = p then a else σ' q := fun _ => rfl
  refine ⟨σ, fun τ => ?_⟩
  have hstep : pos p σ τ 1 = p ++ [a] := by
    rw [pos_succ]; simp [hp, hσdef]
  have key : ∀ k, pos p σ τ (1 + k) = pos (p ++ [a]) σ' τ k := by
    intro k
    rw [pos_add, hstep]
    refine pos_congr ?_ (fun _ _ => rfl) k
    intro q hq
    have hne : q ≠ p := by
      intro hqp
      subst hqp
      have := hq.length_le
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega
    rw [hσdef, if_neg hne]
  rw [play_eq_of_shift key (by simp)]
  exact hσ' τ

/-- If Player II is to move at `p` and every move leads to a position winning for Player I, then
`p` is winning for Player I. -/
theorem IWins_of_all_moves {W : (Nat → A) → Prop} {p : List A} (hp : p.length % 2 = 1)
    (h : ∀ a : A, IWins W (p ++ [a])) : IWins W p := by
  have hF : ∀ a : A, ∀ τ : Strategy A, W (play (p ++ [a]) (Classical.choose (h a)) τ) :=
    fun a => Classical.choose_spec (h a)
  let σ : Strategy A := fun q => if p.length < q.length then
    Classical.choose (h (q.getD p.length default)) q else default
  have hσdef : ∀ q, σ q = if p.length < q.length then
      Classical.choose (h (q.getD p.length default)) q else default := fun _ => rfl
  refine ⟨σ, fun τ => ?_⟩
  have hstep : pos p σ τ 1 = p ++ [τ p] := by
    rw [pos_succ]; simp [hp]
  have key : ∀ k, pos p σ τ (1 + k) = pos (p ++ [τ p]) (Classical.choose (h (τ p))) τ k := by
    intro k
    rw [pos_add, hstep]
    refine pos_congr ?_ (fun _ _ => rfl) k
    intro q hq
    have hlen : p.length < q.length := by
      have := hq.length_le; simp at this; omega
    have hget : q.getD p.length default = τ p := by
      rw [getD_of_prefix hq (by simp)]
      simp [List.getD_eq_getElem?_getD]
    rw [hσdef, if_pos hlen, hget]
  rw [play_eq_of_shift key (by simp)]
  exact hF (τ p) τ

/-- **Gale–Stewart theorem.**  Every open game is determined: if the payoff set `W` is open in
the product topology on `Nat → A` (`A` discrete), then either Player I has a strategy `σ` winning
against every strategy of Player II, or Player II has a strategy `τ` winning against every
strategy of Player I. -/
theorem Gale_Stewart_open {A : Type u} [Inhabited A] (W : (Nat → A) → Prop)
    (hW : IsOpenPayoff W) :
    (∃ σ : Strategy A, ∀ τ : Strategy A, W (play [] σ τ)) ∨
    (∃ τ : Strategy A, ∀ σ : Strategy A, ¬ W (play [] σ τ)) := by
  by_cases hI : IWins W ([] : List A)
  · exact Or.inl hI
  let τ : Strategy A := fun q => if hq : ∃ a : A, ¬ IWins W (q ++ [a]) then Classical.choose hq
    else default
  have hτdef : ∀ q, τ q = if hq : ∃ a : A, ¬ IWins W (q ++ [a]) then Classical.choose hq
      else default := fun _ => rfl
  refine Or.inr ⟨τ, fun σ => ?_⟩
  -- Player II can always move to a position that is still not winning for Player I.
  have hτgood : ∀ q : List A, q.length % 2 = 1 → ¬ IWins W q → ¬ IWins W (q ++ [τ q]) := by
    intro q hq hnw
    have hex : ∃ a : A, ¬ IWins W (q ++ [a]) :=
      Classical.byContradiction fun hc =>
        hnw (IWins_of_all_moves hq fun a =>
          Classical.byContradiction fun hna => hc ⟨a, hna⟩)
    have : τ q = Classical.choose hex := by rw [hτdef, dif_pos hex]
    rw [this]
    exact Classical.choose_spec hex
  -- The invariant: every position along the play is not winning for Player I.
  have hinv : ∀ k, ¬ IWins W (pos ([] : List A) σ τ k) := by
    intro k
    induction k with
    | zero => simpa using hI
    | succ k ih =>
      rw [pos_succ]
      by_cases hpar : (pos ([] : List A) σ τ k).length % 2 = 0
      · rw [if_pos hpar]
        intro hw
        exact ih (IWins_of_move hpar hw)
      · rw [if_neg hpar]
        refine hτgood _ ?_ ih
        omega
  -- If Player I won this play, openness would make some position winning for Player I.
  intro hwin
  obtain ⟨n, hn⟩ := hW _ hwin
  refine hinv n ⟨σ, fun τ₀ => ?_⟩
  refine hn _ (fun i hi => ?_)
  have h1 : play (pos ([] : List A) σ τ n) σ τ₀ i = (pos ([] : List A) σ τ n).getD i default :=
    play_eq_of_lt _ _ _ (by simp; omega)
  have h2 : play ([] : List A) σ τ i = (pos ([] : List A) σ τ n).getD i default :=
    play_eq_getD _ _ _ (by simp; omega)
  rw [h1, h2]

end Frontier

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

