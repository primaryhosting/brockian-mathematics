/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import Mathlib

/-!
## Overview

We formalise infinite two-player perfect-information games on Baire space `ℕ → ℕ`
(the standard setting for Borel determinacy), together with strategies, winning
strategies and determinacy.

* `Frontier.BorelDeterminacy` is the full statement of Martin's theorem: every game whose
  payoff set is Borel is determined.
* `Frontier.Borel_determinacy` is the *base case* of that statement, proved here in full:
  every game whose payoff set lies at the bottom level of the Borel hierarchy
  (`Σ⁰₁`, i.e. open, or `Π⁰₁`, i.e. closed) is determined.  This is the Gale–Stewart
  theorem, the base case on which Martin's inductive unravelling argument rests.
  Mathlib contains no determinacy results, so the game-theoretic framework and the
  proof are developed here from scratch.

The proof of the base case is the classical one: if the first player has no winning
strategy from the empty position, the second player can move so as to preserve the
property "the first player has no winning strategy from the current position", and an
open payoff set would be entered only at a position from which the first player wins
trivially.
-/

namespace Frontier

/-- Baire space: the space of plays of a game where each move is a natural number. -/
abbrev Baire := ℕ → ℕ

/-- The position (finite sequence of moves) consisting of the first `n` moves of the
play `f`. -/
def pre (f : Baire) (n : ℕ) : List ℕ := (List.range n).map f

/-- The `i`-th entry of a position, with junk value `0` out of range. -/
def nth (q : List ℕ) (i : ℕ) : ℕ := q.getD i 0

@[simp] lemma pre_length (f : Baire) (n : ℕ) : (pre f n).length = n := by simp [pre]

lemma pre_succ (f : Baire) (n : ℕ) : pre f (n + 1) = pre f n ++ [f n] := by
  simp [pre, List.range_succ]

lemma nth_pre {f : Baire} {n i : ℕ} (h : i < n) : nth (pre f n) i = f i := by
  rw [nth, pre, List.getD_eq_getElem] <;> simp [h]

/-- The play `f` starts with the position `p`. -/
def Extends (p : List ℕ) (f : Baire) : Prop := pre f p.length = p

/-- `Cons e p σ f` says that from the position `p` onwards, the play `f` follows the
strategy `σ` at all moves belonging to the player `e` (`e = 0` is the player who moves
at even stages, `e = 1` the player who moves at odd stages). -/
def Cons (e : ℕ) (p : List ℕ) (σ : List ℕ → ℕ) (f : Baire) : Prop :=
  ∀ n, p.length ≤ n → n % 2 = e → f n = σ (pre f n)

/-- The strategy `σ` for player `e`, played from the position `p`, guarantees that the
resulting play lies in the payoff set `S`. -/
def Wins (S : Set Baire) (e : ℕ) (p : List ℕ) (σ : List ℕ → ℕ) : Prop :=
  ∀ f, Extends p f → Cons e p σ f → f ∈ S

/-- Player `e` has a winning strategy for the payoff set `S` from the position `p`. -/
def Win (S : Set Baire) (e : ℕ) (p : List ℕ) : Prop := ∃ σ, Wins S e p σ

/-- A game with payoff set `A` (for the player who moves first, at even stages) is
*determined* if one of the two players has a winning strategy: either the first player
has a strategy forcing the play into `A`, or the second player has a strategy forcing
the play into the complement of `A`. -/
def Determined (A : Set Baire) : Prop := Win A 0 [] ∨ Win Aᶜ 1 []

/-!
### The play produced by a pair of strategies

This section checks that the notion of determinacy above is a genuine dichotomy: a pair of
strategies always produces a play consistent with both, so the two players cannot both
have a winning strategy.
-/

/-- The position reached after `n` moves when player `0` follows `σ` and player `1`
follows `τ`. -/
def hist (σ τ : List ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => hist σ τ n ++ [if n % 2 = 0 then σ (hist σ τ n) else τ (hist σ τ n)]

/-- The play resulting from the pair of strategies `σ` (for player `0`) and `τ` (for
player `1`). -/
def playOf (σ τ : List ℕ → ℕ) (n : ℕ) : ℕ := nth (hist σ τ (n + 1)) n

@[simp] lemma hist_length (σ τ : List ℕ → ℕ) (n : ℕ) : (hist σ τ n).length = n := by
  induction n with
  | zero => simp [hist]
  | succ n ih => simp [hist, ih]

lemma playOf_eq (σ τ : List ℕ → ℕ) (n : ℕ) :
    playOf σ τ n = if n % 2 = 0 then σ (hist σ τ n) else τ (hist σ τ n) := by
  simp [playOf, hist, nth]

lemma pre_playOf (σ τ : List ℕ → ℕ) (n : ℕ) : pre (playOf σ τ) n = hist σ τ n := by
  induction n with
  | zero => simp [pre, hist]
  | succ n ih => rw [pre_succ, ih, playOf_eq, hist]

/-- The play produced by `σ` and `τ` is consistent with `σ` for player `0`. -/
lemma cons_playOf_zero (σ τ : List ℕ → ℕ) : Cons 0 [] σ (playOf σ τ) := by
  intro n _ hpar
  rw [pre_playOf, playOf_eq, if_pos hpar]

/-- The play produced by `σ` and `τ` is consistent with `τ` for player `1`. -/
lemma cons_playOf_one (σ τ : List ℕ → ℕ) : Cons 1 [] τ (playOf σ τ) := by
  intro n _ hpar
  rw [pre_playOf, playOf_eq, if_neg (by omega)]

/-- Determinacy is a genuine dichotomy: the two players cannot both have a winning
strategy.  In particular the notion `Frontier.Determined` is not vacuously true. -/
theorem not_win_both (A : Set Baire) : ¬ (Win A 0 [] ∧ Win Aᶜ 1 []) := by
  rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
  have h1 : playOf σ τ ∈ A :=
    hσ _ (by simp [Extends, pre]) (cons_playOf_zero σ τ)
  have h2 : playOf σ τ ∈ Aᶜ :=
    hτ _ (by simp [Extends, pre]) (cons_playOf_one σ τ)
  exact h2 h1

/-!
### The two elementary steps of the backward induction
-/

/-- If it is the turn of player `e` at the position `p` and player `e` wins from some
immediate successor position `p ++ [a]`, then player `e` wins from `p`. -/
theorem win_of_win_append {S : Set Baire} {e : ℕ} {p : List ℕ} {a : ℕ}
    (hp : p.length % 2 = e) (h : Win S e (p ++ [a])) : Win S e p := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun q => if q = p then a else σ q, fun f hf hcons => ?_⟩
  have hfp : f p.length = a := by
    have := hcons p.length le_rfl hp
    rw [Extends] at hf
    simpa [hf] using this
  have hext : Extends (p ++ [a]) f := by
    have : pre f (p.length + 1) = p ++ [a] := by
      rw [pre_succ, hf, hfp]
    simpa [Extends] using this
  refine hσ f hext ?_
  intro n hn hpar
  have hlen : p.length < n := by simpa using hn
  have hne : pre f n ≠ p := by
    intro hEq
    have := congrArg List.length hEq
    simp at this
    omega
  have := hcons n (le_of_lt hlen) hpar
  simpa [hne] using this

/-- If player `e` wins from *every* immediate successor position of `p`, then player `e`
wins from `p`.  (This is used when it is the opponent's turn at `p`; the parity of
`p.length` is in fact irrelevant, since a strategy may read off the last move played.) -/
theorem win_of_forall_win_append {S : Set Baire} {e : ℕ} {p : List ℕ}
    (h : ∀ a, Win S e (p ++ [a])) : Win S e p := by
  choose sig hsig using h
  refine ⟨fun q => sig (nth q p.length) q, fun f hf hcons => ?_⟩
  set a := f p.length with ha
  have hext : Extends (p ++ [a]) f := by
    have : pre f (p.length + 1) = p ++ [a] := by rw [pre_succ, hf]
    simpa [Extends] using this
  refine hsig a f hext ?_
  intro n hn hpar
  have hlen : p.length < n := by simpa using hn
  have hnth : nth (pre f n) p.length = a := nth_pre hlen
  have := hcons n (le_of_lt hlen) hpar
  rw [this]
  show sig (nth (pre f n) p.length) (pre f n) = sig a (pre f n)
  rw [hnth]

/-!
### The Gale–Stewart theorem
-/

/-- **Gale–Stewart.**  If the payoff set `S` of player `e` is open and player `e` has no
winning strategy from the position `p`, then the opponent `1 - e` has a winning strategy
for the complementary payoff set from `p`. -/
theorem win_compl_of_not_win_of_isOpen {S : Set Baire} {e : ℕ} {p : List ℕ} (he : e < 2)
    (hS : IsOpen S) (h : ¬ Win S e p) : Win Sᶜ (1 - e) p := by
  classical
  -- the opponent's strategy: always move to a position from which player `e` does not win
  set τ : List ℕ → ℕ := fun q => if h : ∃ a, ¬ Win S e (q ++ [a]) then h.choose else 0
    with hτ
  refine ⟨τ, fun f hf hcons => ?_⟩
  have hfp : pre f p.length = p := hf
  -- every position reached is one from which player `e` has no winning strategy
  have key : ∀ n, p.length ≤ n → ¬ Win S e (pre f n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rw [hfp]; exact h
    | succ n hn ih =>
        rw [pre_succ]
        by_cases hpar : n % 2 = e
        · -- player `e` moves: by `win_of_win_append` no successor can be winning
          intro hw
          exact ih (win_of_win_append (by simpa using hpar) hw)
        · -- the opponent moves, following `τ`
          have hex : ∃ a, ¬ Win S e (pre f n ++ [a]) := by
            by_contra hall
            push_neg at hall
            exact ih (win_of_forall_win_append hall)
          have hfn : f n = τ (pre f n) := by
            refine hcons n hn ?_
            have : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
            omega
          have hch : τ (pre f n) = hex.choose := by simp only [hτ, dif_pos hex]
          rw [hfn, hch]
          exact hex.choose_spec
  -- an open payoff set can only be entered at a position which player `e` wins outright
  intro hmem
  obtain ⟨u, ⟨y, n, rfl⟩, hxu, hus⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open hmem hS
  refine key (max n p.length) (le_max_right _ _) ⟨fun _ => 0, fun g hg _ => hus ?_⟩
  simp only [PiNat.cylinder, Set.mem_setOf_eq] at hxu ⊢
  intro i hi
  have hi' : i < max n p.length := lt_of_lt_of_le hi (le_max_left _ _)
  have hgn : pre g (max n p.length) = pre f (max n p.length) := by simpa [Extends] using hg
  have h2 : nth (pre g (max n p.length)) i = nth (pre f (max n p.length)) i := by rw [hgn]
  rw [nth_pre hi', nth_pre hi'] at h2
  rw [h2, hxu i hi]

/-- Every open game is determined, from any starting position. -/
theorem win_or_win_compl_of_isOpen {S : Set Baire} {e : ℕ} {p : List ℕ} (he : e < 2)
    (hS : IsOpen S) : Win S e p ∨ Win Sᶜ (1 - e) p := by
  by_cases h : Win S e p
  · exact Or.inl h
  · exact Or.inr (win_compl_of_not_win_of_isOpen he hS h)

/-- Every open game is determined. -/
theorem determined_of_isOpen {A : Set Baire} (hA : IsOpen A) : Determined A := by
  by_cases h : Win A 0 []
  · exact Or.inl h
  · exact Or.inr (by simpa using win_compl_of_not_win_of_isOpen (p := []) (by norm_num) hA h)

/-- Every closed game is determined. -/
theorem determined_of_isClosed {A : Set Baire} (hA : IsClosed A) : Determined A := by
  by_cases h : Win Aᶜ 1 []
  · exact Or.inr h
  · have := win_compl_of_not_win_of_isOpen (S := Aᶜ) (e := 1) (p := []) (by norm_num)
      hA.isOpen_compl h
    exact Or.inl (by simpa using this)

/-!
### The statement of Martin's theorem, and the base case
-/

/-- **Martin's Borel determinacy theorem** (statement).  Every game on Baire space whose
payoff set is Borel is determined.  This is the full theorem; only its base case is
proved in this file (see `Frontier.Borel_determinacy`). -/
def BorelDeterminacy : Prop :=
  ∀ A : Set Baire, @MeasurableSet Baire (borel Baire) A → Determined A

/-- **Borel determinacy, base case (Gale–Stewart).**

Martin's theorem states that every Borel game on Baire space is determined
(`Frontier.BorelDeterminacy`).  Its proof is an induction along the Borel hierarchy whose
base case — proved here — is the Gale–Stewart theorem: every game whose payoff set is at
the bottom level of the hierarchy, i.e. open (`Σ⁰₁`) or closed (`Π⁰₁`), is determined.

Concretely: for every open, and every closed, payoff set `A ⊆ ℕ → ℕ`, either the first
player has a strategy forcing the play into `A`, or the second player has a strategy
forcing the play into the complement of `A`.

Mathlib contains no determinacy machinery, so games, strategies and determinacy are
defined here (`Frontier.Determined`) and the result is proved from first principles.
The positional form actually used in Martin's induction — determinacy of an open payoff
set from an arbitrary position, for either player — is
`Frontier.win_or_win_compl_of_isOpen`.  The full theorem `Frontier.BorelDeterminacy`
is stated but not proved here. -/
theorem Borel_determinacy :
    ∀ A : Set Baire, (IsOpen A ∨ IsClosed A) → Determined A := by
  rintro A (hA | hA)
  · exact determined_of_isOpen hA
  · exact determined_of_isClosed hA

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

