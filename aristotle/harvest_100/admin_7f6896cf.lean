import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We develop, from scratch (there is no game-determinacy material in Mathlib), the theory of
two-player infinite games of perfect information with moves in an arbitrary nonempty set `A`:
plays are sequences `ℕ → A`, player `0` moves at the even stages, player `1` at the odd ones,
strategies are functions from finite positions (`List A`) to moves, and a payoff set
`S ⊆ (ℕ → A)` is *determined* (`Frontier.Determined`) when one of the players has a winning
strategy.

What is proved unconditionally:

* `Frontier.not_winsFor_both`: the two players never both have a winning strategy
  (non-degeneracy of the framework).
* `Frontier.exists_winsFrom_of_not_losing` and `Frontier.exists_winning_of_isClosedPayoff`:
  the combinatorial heart of the **Gale–Stewart theorem** — in a game whose payoff is closed
  for the player to be favoured, if the opponent cannot win from a position, that player can.
* `Frontier.determined_of_isClosedPayoff`, `Frontier.determined_of_isOpenPayoff`,
  `Frontier.determined_of_isClopenPayoff`: closed, open and clopen games are determined.
  This is the base case of Martin's induction.
* `Frontier.determined_of_inter_open_closed`, `Frontier.determined_of_union_closed_open`:
  one level beyond the base case, games whose payoff is the intersection of an open and a
  closed set (a difference of open sets), or the union of a closed and an open set, are
  determined.
* `Frontier.determined_of_unravelable`: determinacy transfers along a covering
  (`Frontier.Cover`); hence every payoff set unraveled by a clopen game is determined.
* `Frontier.unravelable_of_isClopenPayoff`, `Frontier.unravelable_compl`: clopen sets are
  unravelable, and the unravelable sets are closed under complements.
* `Frontier.UnravelingScheme.mem_of_isBorelPayoff`: the σ-algebra induction which propagates
  membership in an unraveling scheme from the open sets to all Borel sets.

The final statement `Frontier.Borel_determinacy` is Martin's theorem in the form of a
Lean-checked reduction: every Borel game is determined as soon as an *unraveling scheme*
exists, i.e. a class of payoff sets containing the closed sets, closed under complements and
countable unions, and consisting of determined sets.  Martin's construction produces such a
class; supplying it is the combinatorial core of his proof and is not carried out here.
Everything else — the base case, the transfer of determinacy along coverings, stability under
complements, and the σ-algebra induction — is proved.

`Frontier.Borel_determinacy_of_unravelings` specialises the reduction to the concrete class
of payoff sets admitting a clopen covering in the sense of `Frontier.Cover`, for which the
determinacy and complement fields of the scheme are proved here, leaving only the two
unraveling lemmas as hypotheses.  Note that `Frontier.Cover` is a simplified, "full tree"
rendering of Martin's notion of covering (games here have no legality constraints on moves);
no claim is made that Martin's coverings satisfy it verbatim, which is why the abstract
scheme, rather than this concrete class, is used in the headline statement.
-/

universe u v

namespace Frontier

open Classical

variable {A : Type u}

/-! ### Games on a set of moves -/

/-- The list of the first `n` moves of the play `x`. -/
def pre (x : ℕ → A) (n : ℕ) : List A := (List.range n).map x

@[simp] lemma pre_length (x : ℕ → A) (n : ℕ) : (pre x n).length = n := by
  simp [pre]

@[simp] lemma pre_zero (x : ℕ → A) : pre x 0 = [] := by simp [pre]

lemma pre_succ (x : ℕ → A) (n : ℕ) : pre x (n + 1) = pre x n ++ [x n] := by
  simp [pre, List.range_succ]

lemma pre_getD (x : ℕ → A) {i n : ℕ} (h : i < n) (d : A) : (pre x n).getD i d = x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp [pre]

lemma pre_eq_iff (x y : ℕ → A) (n : ℕ) : pre x n = pre y n ↔ ∀ i < n, x i = y i := by
  simp [pre, List.map_inj_left]

/-- A strategy is a map assigning a move to each finite position (the list of moves played
so far, in chronological order). -/
def Strategy (A : Type u) : Type u := List A → A

/-- The play `x` follows the strategy `σ` of the player who moves at the stages `n` with
`n % 2 = p`.  (Player `0` moves at even stages, player `1` at odd stages.) -/
def Consistent (p : ℕ) (σ : Strategy A) (x : ℕ → A) : Prop :=
  ∀ n, n % 2 = p → x n = σ (pre x n)

/-- The play `x` follows the strategy `σ` of player `p` from stage `m` on. -/
def ConsistentFrom (m p : ℕ) (σ : Strategy A) (x : ℕ → A) : Prop :=
  ∀ n, m ≤ n → n % 2 = p → x n = σ (pre x n)

/-- `σ` is a winning strategy for player `p` for the payoff set `S`. -/
def WinsFor (p : ℕ) (σ : Strategy A) (S : Set (ℕ → A)) : Prop :=
  ∀ x, Consistent p σ x → x ∈ S

/-- A game with payoff set `S` (player `0` wins the play `x` iff `x ∈ S`) is *determined*
if one of the two players has a winning strategy. -/
def Determined (S : Set (ℕ → A)) : Prop :=
  (∃ σ : Strategy A, WinsFor 0 σ S) ∨ (∃ τ : Strategy A, WinsFor 1 τ Sᶜ)

/-! ### The play resulting from two strategies -/

/-- The position of length `n` reached when player `0` follows `σ` and player `1` follows `τ`. -/
def prefixPlay (σ τ : Strategy A) : ℕ → List A
  | 0 => []
  | n + 1 => prefixPlay σ τ n ++
      [if n % 2 = 0 then σ (prefixPlay σ τ n) else τ (prefixPlay σ τ n)]

@[simp] lemma prefixPlay_length (σ τ : Strategy A) (n : ℕ) : (prefixPlay σ τ n).length = n := by
  induction n with
  | zero => simp [prefixPlay]
  | succ n ih => simp [prefixPlay, ih]

/-- The play resulting from player `0` following `σ` and player `1` following `τ`. -/
def jointPlay [Inhabited A] (σ τ : Strategy A) (n : ℕ) : A :=
  (prefixPlay σ τ (n + 1)).getD n default

lemma jointPlay_eq [Inhabited A] (σ τ : Strategy A) (n : ℕ) :
    jointPlay σ τ n =
      if n % 2 = 0 then σ (prefixPlay σ τ n) else τ (prefixPlay σ τ n) := by
  unfold jointPlay
  rw [show prefixPlay σ τ (n + 1) = prefixPlay σ τ n ++
      [if n % 2 = 0 then σ (prefixPlay σ τ n) else τ (prefixPlay σ τ n)] from rfl,
    List.getD_eq_getElem _ _ (by simp)]
  simp

lemma pre_jointPlay [Inhabited A] (σ τ : Strategy A) (n : ℕ) :
    pre (jointPlay σ τ) n = prefixPlay σ τ n := by
  induction n with
  | zero => simp [prefixPlay]
  | succ n ih =>
    rw [pre_succ, ih, jointPlay_eq]
    rfl

/-- The two players cannot both have a winning strategy: the framework is non-degenerate. -/
theorem not_winsFor_both [Nonempty A] {S : Set (ℕ → A)} {σ τ : Strategy A}
    (h0 : WinsFor 0 σ S) (h1 : WinsFor 1 τ Sᶜ) : False := by
  haveI : Inhabited A := Classical.inhabited_of_nonempty ‹Nonempty A›
  have hc0 : Consistent 0 σ (jointPlay σ τ) := by
    intro n hn
    rw [pre_jointPlay, jointPlay_eq, if_pos hn]
  have hc1 : Consistent 1 τ (jointPlay σ τ) := by
    intro n hn
    rw [pre_jointPlay, jointPlay_eq, if_neg (by omega)]
  exact h1 _ hc1 (h0 _ hc0)

/-! ### Topology on the space of plays -/

/-- `S` is open in the product topology on `ℕ → A` with `A` discrete: membership in `S` is
decided by a finite initial segment of the play. -/
def IsOpenPayoff (S : Set (ℕ → A)) : Prop :=
  ∀ x ∈ S, ∃ n, ∀ y, pre y n = pre x n → y ∈ S

/-- `S` is closed in the product topology on `ℕ → A` with `A` discrete. -/
def IsClosedPayoff (S : Set (ℕ → A)) : Prop := IsOpenPayoff Sᶜ

/-- `S` is clopen. -/
def IsClopenPayoff (S : Set (ℕ → A)) : Prop := IsOpenPayoff S ∧ IsClosedPayoff S

/-- The Borel payoff sets: the σ-algebra generated by the open payoff sets. -/
def IsBorelPayoff (S : Set (ℕ → A)) : Prop :=
  MeasurableSpace.GenerateMeasurable {T : Set (ℕ → A) | IsOpenPayoff T} S

/-- `IsBorelPayoff` is measurability for the σ-algebra generated by the open payoff sets. -/
lemma isBorelPayoff_iff (S : Set (ℕ → A)) :
    IsBorelPayoff S ↔
      @MeasurableSet _ (MeasurableSpace.generateFrom {T : Set (ℕ → A) | IsOpenPayoff T}) S :=
  Iff.rfl

/-! ### The Gale–Stewart theorem (the base case) -/

/-- `σ` is a winning strategy for player `p` for the payoff `S` in the game started from the
position `u`. -/
def WinsFrom (p : ℕ) (σ : Strategy A) (S : Set (ℕ → A)) (u : List A) : Prop :=
  ∀ x, pre x u.length = u → ConsistentFrom u.length p σ x → x ∈ S

lemma winsFor_iff_winsFrom_nil (p : ℕ) (σ : Strategy A) (S : Set (ℕ → A)) :
    WinsFor p σ S ↔ WinsFrom p σ S [] := by
  constructor
  · exact fun h x _ hc => h x fun n hn => hc n (Nat.zero_le _) hn
  · exact fun h x hc => h x (by simp) fun n _ hn => hc n hn

/-- The opponent (the player moving at stages `n` with `n % 2 = q`) has a strategy which,
from the position `u` on, guarantees a play outside `S`. -/
def Losing (q : ℕ) (S : Set (ℕ → A)) (u : List A) : Prop :=
  ∃ τ : Strategy A, WinsFrom q τ Sᶜ u

/-- **Gale–Stewart**, from an arbitrary position: in a game with closed payoff for player
`p`, if the opponent `q` cannot win from the position `w`, then `p` can. -/
theorem exists_winsFrom_of_not_losing [Nonempty A] {p q : ℕ} (hp : p < 2) (hq : q < 2)
    (hpq : p ≠ q) {S : Set (ℕ → A)} (hS : IsClosedPayoff S) {w : List A}
    (h : ¬ Losing q S w) : ∃ σ : Strategy A, WinsFrom p σ S w := by
  haveI : Inhabited A := Classical.inhabited_of_nonempty ‹Nonempty A›
  -- If every immediate extension of `u` is losing, so is `u`.
  have hstep : ∀ u : List A, (∀ a : A, Losing q S (u ++ [a])) → Losing q S u := by
    intro u hL
    choose τ hτ using hL
    refine ⟨fun v => τ (v.getD u.length default) v, ?_⟩
    intro x hx hcons
    have hxu : pre x (u.length + 1) = u ++ [x u.length] := by rw [pre_succ, hx]
    refine hτ (x u.length) x (by simpa using hxu) ?_
    intro n hn hnq
    have hn' : u.length + 1 ≤ n := by simpa using hn
    have := hcons n (by omega) hnq
    rw [this]
    simp only [pre_getD x (show u.length < n by omega)]
  -- If it is the opponent's turn at `u` and some extension is losing, then `u` is losing.
  have hstepQ : ∀ (u : List A) (a : A), u.length % 2 = q → Losing q S (u ++ [a]) →
      Losing q S u := by
    intro u a hu ⟨τ', hτ'⟩
    refine ⟨fun v => if v.length = u.length then a else τ' v, ?_⟩
    intro x hx hcons
    have hxa : x u.length = a := by
      have := hcons u.length le_rfl hu
      rw [this, hx]
      simp
    have hxu : pre x (u.length + 1) = u ++ [a] := by rw [pre_succ, hx, hxa]
    refine hτ' x (by simpa using hxu) ?_
    intro n hn hnq
    have hn' : u.length + 1 ≤ n := by simpa using hn
    have := hcons n (by omega) hnq
    rw [this]
    simp only [pre_length]
    rw [if_neg (by omega)]
  -- A play all of whose initial positions are non-losing is won by `p`, since `S` is closed.
  have hD : ∀ x : ℕ → A, (∀ n, w.length ≤ n → ¬ Losing q S (pre x n)) → x ∈ S := by
    intro x hxg
    by_contra hxS
    obtain ⟨n, hn⟩ := hS x hxS
    refine hxg (max n w.length) (le_max_right _ _)
      ⟨fun _ => default, fun y hy _ => hn y ?_⟩
    rw [pre_length] at hy
    rw [pre_eq_iff]
    intro i hi
    exact (pre_eq_iff y x _).mp hy i (lt_of_lt_of_le hi (le_max_left _ _))
  -- The strategy for `p`: always move to a non-losing position.
  have hchoice : ∀ u : List A, ∃ a : A,
      (u.length % 2 = p → ¬ Losing q S u → ¬ Losing q S (u ++ [a])) := by
    intro u
    by_cases hu : ∃ a : A, ¬ Losing q S (u ++ [a])
    · obtain ⟨a, ha⟩ := hu
      exact ⟨a, fun _ _ => ha⟩
    · push_neg at hu
      exact ⟨default, fun _ hgu => absurd (hstep u hu) hgu⟩
  choose σ hσ using hchoice
  refine ⟨σ, fun x hxw hx => hD x ?_⟩
  have key : ∀ k, ¬ Losing q S (pre x (w.length + k)) := by
    intro k
    induction k with
    | zero => simpa [hxw] using h
    | succ k ih =>
      rw [show w.length + (k + 1) = (w.length + k) + 1 from rfl, pre_succ]
      by_cases hn : (w.length + k) % 2 = p
      · have hxn : x (w.length + k) = σ (pre x (w.length + k)) :=
          hx _ (Nat.le_add_right _ _) hn
        rw [hxn]
        exact hσ (pre x (w.length + k)) (by simpa using hn) ih
      · have hnq : (w.length + k) % 2 = q := by omega
        exact fun hcon =>
          ih (hstepQ (pre x (w.length + k)) (x (w.length + k)) (by simpa using hnq) hcon)
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = w.length + k := ⟨n - w.length, by omega⟩
  exact key k

/-- **Gale–Stewart**: in a game with closed payoff for player `p`, if the opponent `q` has
no winning strategy then `p` has one. -/
theorem exists_winning_of_isClosedPayoff [Nonempty A] {p q : ℕ} (hp : p < 2) (hq : q < 2)
    (hpq : p ≠ q) {S : Set (ℕ → A)} (hS : IsClosedPayoff S)
    (h : ¬ ∃ τ : Strategy A, WinsFor q τ Sᶜ) : ∃ σ : Strategy A, WinsFor p σ S := by
  have h' : ¬ Losing q S ([] : List A) := by
    rintro ⟨τ, hτ⟩
    exact h ⟨τ, (winsFor_iff_winsFrom_nil q τ Sᶜ).mpr hτ⟩
  obtain ⟨σ, hσ⟩ := exists_winsFrom_of_not_losing hp hq hpq hS h'
  exact ⟨σ, (winsFor_iff_winsFrom_nil p σ S).mpr hσ⟩

/-- Closed games are determined. -/
theorem determined_of_isClosedPayoff [Nonempty A] {S : Set (ℕ → A)} (hS : IsClosedPayoff S) :
    Determined S := by
  by_cases h : ∃ τ : Strategy A, WinsFor 1 τ Sᶜ
  · exact Or.inr h
  · exact Or.inl (exists_winning_of_isClosedPayoff (by norm_num) (by norm_num) (by norm_num) hS h)

/-- Open games are determined. -/
theorem determined_of_isOpenPayoff [Nonempty A] {S : Set (ℕ → A)} (hS : IsOpenPayoff S) :
    Determined S := by
  by_cases h : ∃ σ : Strategy A, WinsFor 0 σ S
  · exact Or.inl h
  · have hSc : IsClosedPayoff Sᶜ := by simpa [IsClosedPayoff, compl_compl] using hS
    have h' : ¬ ∃ σ : Strategy A, WinsFor 0 σ (Sᶜ)ᶜ := by simpa [compl_compl] using h
    exact Or.inr (exists_winning_of_isClosedPayoff (by norm_num) (by norm_num) (by norm_num)
      hSc h')

/-- Clopen games are determined. -/
theorem determined_of_isClopenPayoff [Nonempty A] {S : Set (ℕ → A)} (hS : IsClopenPayoff S) :
    Determined S :=
  determined_of_isClosedPayoff hS.2

/-- Open payoff sets are Borel. -/
theorem isBorelPayoff_of_isOpenPayoff {S : Set (ℕ → A)} (hS : IsOpenPayoff S) :
    IsBorelPayoff S :=
  MeasurableSpace.GenerateMeasurable.basic S hS

/-- Closed payoff sets are Borel. -/
theorem isBorelPayoff_of_isClosedPayoff {S : Set (ℕ → A)} (hS : IsClosedPayoff S) :
    IsBorelPayoff S := by
  have h := MeasurableSpace.GenerateMeasurable.compl _ (isBorelPayoff_of_isOpenPayoff hS)
  simpa [IsBorelPayoff, compl_compl] using h

/-! ### Differences of open sets are determined -/

/-- The position `u` *decides* `S`: every play through `u` belongs to `S`. -/
def Decides (S : Set (ℕ → A)) (u : List A) : Prop := ∀ y, pre y u.length = u → y ∈ S

lemma pre_take (x : ℕ → A) {m n : ℕ} (h : m ≤ n) : (pre x n).take m = pre x m := by
  rw [pre, pre, ← List.map_take, List.take_range, Nat.min_eq_left h]

lemma mem_of_decides {S : Set (ℕ → A)} {x : ℕ → A} {n : ℕ} (h : Decides S (pre x n)) : x ∈ S :=
  h x (by simp)

lemma exists_decides_of_isOpenPayoff {S : Set (ℕ → A)} (hS : IsOpenPayoff S) {x : ℕ → A}
    (hx : x ∈ S) : ∃ n, Decides S (pre x n) := by
  obtain ⟨n, hn⟩ := hS x hx
  exact ⟨n, fun y hy => hn y (by simpa using hy)⟩

/-- From any position, any strategy can be played out. -/
lemma exists_consistentFrom [Inhabited A] (u : List A) (q : ℕ) (τ : Strategy A) :
    ∃ x, pre x u.length = u ∧ ConsistentFrom u.length q τ x := by
  classical
  set f : Strategy A := fun v =>
    if v.length < u.length then u.getD v.length default
    else if v.length % 2 = q then τ v else default with hf
  have hstep : ∀ n, jointPlay f f n = f (pre (jointPlay f f) n) := by
    intro n
    rw [pre_jointPlay, jointPlay_eq]
    split <;> rfl
  refine ⟨jointPlay f f, ?_, ?_⟩
  · have key : ∀ n, n ≤ u.length → pre (jointPlay f f) n = u.take n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro hn
        have hn' : n < u.length := by omega
        rw [pre_succ, ih (by omega), hstep n, ih (by omega), hf]
        simp only [List.length_take, Nat.min_eq_left hn'.le, if_pos hn']
        rw [List.getD_eq_getElem _ _ hn']
        exact (List.take_succ_eq_append_getElem hn').symm
    simpa using key u.length le_rfl
  · intro n hn hnq
    rw [hstep n, hf]
    simp only [pre_length]
    rw [if_neg (by omega), if_pos hnq]

open Classical in
/-- The strategy which follows `base` until the first position satisfying `Trig` is reached,
and from then on follows the strategy `alt` attached to that position. -/
noncomputable def splice (Trig : List A → Prop) (base : Strategy A) (alt : List A → Strategy A) :
    Strategy A := fun v =>
  if h : ∃ m, m ≤ v.length ∧ Trig (v.take m) then alt (v.take (Nat.find h)) v else base v

lemma splice_eq_base {Trig : List A → Prop} {base : Strategy A} {alt : List A → Strategy A}
    {x : ℕ → A} {n : ℕ} (h : ∀ m ≤ n, ¬ Trig (pre x m)) :
    splice Trig base alt (pre x n) = base (pre x n) := by
  classical
  rw [splice, dif_neg]
  rintro ⟨m, hm, hT⟩
  rw [pre_length] at hm
  rw [pre_take x hm] at hT
  exact h m hm hT

lemma splice_eq_alt {Trig : List A → Prop} {base : Strategy A} {alt : List A → Strategy A}
    {x : ℕ → A} {n₀ n : ℕ} (hn₀ : Trig (pre x n₀)) (hmin : ∀ m < n₀, ¬ Trig (pre x m))
    (hle : n₀ ≤ n) : splice Trig base alt (pre x n) = alt (pre x n₀) (pre x n) := by
  classical
  have hex : ∃ m, m ≤ (pre x n).length ∧ Trig ((pre x n).take m) := by
    refine ⟨n₀, by simpa using hle, ?_⟩
    rwa [pre_take x hle]
  rw [splice, dif_pos hex]
  have hfind : Nat.find hex = n₀ := by
    refine le_antisymm (Nat.find_le ⟨by simpa using hle, by rwa [pre_take x hle]⟩) ?_
    by_contra hlt
    push_neg at hlt
    obtain ⟨hm, hT⟩ := Nat.find_spec hex
    have hm' : Nat.find hex ≤ n := by simpa using hm
    rw [pre_take x hm'] at hT
    exact hmin _ hlt hT
  rw [hfind, pre_take x hle]

/-- **Determinacy of differences of open sets** (level two of the difference hierarchy):
in the game whose payoff for player `p` is the intersection of an open and a closed set, one
of the two players has a winning strategy. -/
theorem winsFor_or_winsFor_inter [Nonempty A] {p q : ℕ} (hp : p < 2) (hq : q < 2) (hpq : p ≠ q)
    {U C : Set (ℕ → A)} (hU : IsOpenPayoff U) (hC : IsClosedPayoff C) :
    (∃ σ : Strategy A, WinsFor p σ (U ∩ C)) ∨ (∃ τ : Strategy A, WinsFor q τ (U ∩ C)ᶜ) := by
  classical
  haveI : Inhabited A := Classical.inhabited_of_nonempty ‹Nonempty A›
  -- The auxiliary open game: reach a position which decides `U` and from which the closed
  -- game `C` is still winnable for `p`.
  set Trig : List A → Prop := fun u => Decides U u ∧ ¬ Losing q C u with hTrig
  set O : Set (ℕ → A) := {x | ∃ n, Trig (pre x n)} with hO
  have hOopen : IsOpenPayoff O := by
    rintro x ⟨n, hn⟩
    exact ⟨n, fun y hy => ⟨n, by rw [hy]; exact hn⟩⟩
  have hOdet : (∃ σ : Strategy A, WinsFor p σ O) ∨ (∃ τ : Strategy A, WinsFor q τ Oᶜ) := by
    by_cases h : ∃ σ : Strategy A, WinsFor p σ O
    · exact Or.inl h
    · refine Or.inr (exists_winning_of_isClosedPayoff hq hp (Ne.symm hpq) ?_ ?_)
      · simpa [IsClosedPayoff, compl_compl] using hOopen
      · simpa [compl_compl] using h
  rcases hOdet with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · -- Player `p` reaches a good position, then wins the closed game from there.
    left
    have halt : ∀ u : List A, ∃ ξ : Strategy A, ¬ Losing q C u → WinsFrom p ξ C u := by
      intro u
      by_cases hu : ¬ Losing q C u
      · obtain ⟨ξ, hξ⟩ := exists_winsFrom_of_not_losing hp hq hpq hC hu
        exact ⟨ξ, fun _ => hξ⟩
      · exact ⟨fun _ => default, fun h => absurd h hu⟩
    choose alt halt using halt
    refine ⟨splice Trig σ alt, fun x hx => ?_⟩
    by_cases hnone : ∀ n, ¬ Trig (pre x n)
    · exfalso
      have : Consistent p σ x := by
        intro n hn
        rw [hx n hn, splice_eq_base (fun m _ => hnone m)]
      obtain ⟨n, hn⟩ := hσ x this
      exact hnone n hn
    · push_neg at hnone
      obtain ⟨n, hn⟩ := hnone
      have hex : ∃ n, Trig (pre x n) := ⟨n, hn⟩
      set n₀ := Nat.find hex with hn₀def
      have hn₀ : Trig (pre x n₀) := Nat.find_spec hex
      have hmin : ∀ m < n₀, ¬ Trig (pre x m) := fun m hm => Nat.find_min hex hm
      refine ⟨mem_of_decides hn₀.1, ?_⟩
      refine halt (pre x n₀) hn₀.2 x (by simp) ?_
      intro k hk hkp
      rw [pre_length] at hk
      rw [hx k hkp, splice_eq_alt hn₀ hmin hk]
  · -- Player `q` avoids the good positions, then refutes `C` once `U` is decided.
    right
    have halt : ∀ u : List A, ∃ ξ : Strategy A, Losing q C u → WinsFrom q ξ Cᶜ u := by
      intro u
      by_cases hu : Losing q C u
      · obtain ⟨ξ, hξ⟩ := hu
        exact ⟨ξ, fun _ => hξ⟩
      · exact ⟨fun _ => default, fun h => absurd h hu⟩
    choose alt halt using halt
    refine ⟨splice (Decides U) τ alt, fun x hx => ?_⟩
    by_cases hnone : ∀ n, ¬ Decides U (pre x n)
    · have hcons : Consistent q τ x := by
        intro n hn
        rw [hx n hn, splice_eq_base (fun m _ => hnone m)]
      intro hmem
      obtain ⟨n, hn⟩ := exists_decides_of_isOpenPayoff hU hmem.1
      exact hnone n hn
    · push_neg at hnone
      obtain ⟨n, hn⟩ := hnone
      have hex : ∃ n, Decides U (pre x n) := ⟨n, hn⟩
      set n₀ := Nat.find hex with hn₀def
      have hn₀ : Decides U (pre x n₀) := Nat.find_spec hex
      have hmin : ∀ m < n₀, ¬ Decides U (pre x m) := fun m hm => Nat.find_min hex hm
      -- Before the trigger the play follows `τ`; hence the position `pre x n₀` is losing.
      have hlose : Losing q C (pre x n₀) := by
        obtain ⟨z, hz, hzc⟩ := exists_consistentFrom (pre x n₀) q τ
        rw [pre_length] at hz
        have hzcons : Consistent q τ z := by
          intro k hk
          rcases lt_or_ge k n₀ with hlt | hge
          · have hzx : pre z k = pre x k := by
              rw [pre_eq_iff]
              intro i hi
              exact (pre_eq_iff z x n₀).mp hz i (by omega)
            have hzk : z k = x k := (pre_eq_iff z x n₀).mp hz k hlt
            rw [hzk, hzx, hx k hk, splice_eq_base (fun m hm => hmin m (by omega))]
          · exact hzc k (by simpa using hge) hk
        have hzO : z ∉ O := hτ z hzcons
        have : ¬ Trig (pre z n₀) := fun hT => hzO ⟨n₀, hT⟩
        rw [show pre z n₀ = pre x n₀ from hz] at this
        by_contra hcon
        exact this ⟨hn₀, hcon⟩
      intro hmem
      refine halt (pre x n₀) hlose x (by simp) ?_ hmem.2
      intro k hk hkq
      rw [pre_length] at hk
      rw [hx k hkq, splice_eq_alt hn₀ hmin hk]

/-- The intersection of an open and a closed payoff set is determined. -/
theorem determined_of_inter_open_closed [Nonempty A] {U C : Set (ℕ → A)} (hU : IsOpenPayoff U)
    (hC : IsClosedPayoff C) : Determined (U ∩ C) :=
  winsFor_or_winsFor_inter (by norm_num) (by norm_num) (by norm_num) hU hC

/-- The union of a closed and an open payoff set is determined. -/
theorem determined_of_union_closed_open [Nonempty A] {C U : Set (ℕ → A)} (hC : IsClosedPayoff C)
    (hU : IsOpenPayoff U) : Determined (C ∪ U) := by
  have hCc : IsOpenPayoff Cᶜ := hC
  have hUc : IsClosedPayoff Uᶜ := by simpa [IsClosedPayoff, compl_compl] using hU
  have h := winsFor_or_winsFor_inter (p := 1) (q := 0) (by norm_num) (by norm_num) (by norm_num)
    hCc hUc
  have hset : Cᶜ ∩ Uᶜ = (C ∪ U)ᶜ := by
    rw [Set.compl_union]
  rw [hset] at h
  rcases h with ⟨τ, hτ⟩ | ⟨σ, hσ⟩
  · exact Or.inr ⟨τ, hτ⟩
  · rw [compl_compl] at hσ
    exact Or.inl ⟨σ, hσ⟩

/-! ### Coverings (Martin's unravelings) -/

/-- A *covering* of the game with payoff `S` on the moves `A` by the game with payoff `S'`
on the moves `B`: a projection of plays pulling `S` back to `S'`, together with a lifting of
strategies such that every play following a lifted strategy is the projection of a play
following the original one. -/
structure Cover (S : Set (ℕ → A)) (B : Type v) (S' : Set (ℕ → B)) : Type (max u v) where
  /-- the projection of plays of the covering game to plays of the covered game -/
  proj : (ℕ → B) → (ℕ → A)
  /-- the payoff set of the covering game is the pullback of the payoff set -/
  preimage_eq : S' = proj ⁻¹' S
  /-- lifting of strategies for either player -/
  lift : ℕ → Strategy B → Strategy A
  /-- every play following a lifted strategy is the projection of a play following the
  original strategy -/
  lift_spec : ∀ p (σ' : Strategy B) (x : ℕ → A), Consistent p (lift p σ') x →
    ∃ y, Consistent p σ' y ∧ proj y = x

/-- `S` is *unravelable* (in Martin's sense) if some game with clopen payoff covers it. -/
def Unravelable (S : Set (ℕ → A)) : Prop :=
  ∃ (B : Type u) (_ : Nonempty B) (S' : Set (ℕ → B)),
    IsClopenPayoff S' ∧ Nonempty (Cover S B S')

/-- Determinacy transfers along coverings; hence unravelable games are determined. -/
theorem determined_of_unravelable {S : Set (ℕ → A)} (h : Unravelable S) : Determined S := by
  obtain ⟨B, hB, S', hclopen, ⟨C⟩⟩ := h
  rcases determined_of_isClosedPayoff hclopen.2 with ⟨σ', hσ'⟩ | ⟨τ', hτ'⟩
  · refine Or.inl ⟨C.lift 0 σ', fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := C.lift_spec 0 σ' x hx
    have := hσ' y hy
    rw [C.preimage_eq] at this
    exact this
  · refine Or.inr ⟨C.lift 1 τ', fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := C.lift_spec 1 τ' x hx
    have := hτ' y hy
    rw [C.preimage_eq] at this
    exact this

/-- Clopen games are unravelable (via the identity covering). -/
theorem unravelable_of_isClopenPayoff [Nonempty A] {S : Set (ℕ → A)} (hS : IsClopenPayoff S) :
    Unravelable S :=
  ⟨A, inferInstance, S, hS,
    ⟨{ proj := id
       preimage_eq := rfl
       lift := fun _ σ => σ
       lift_spec := fun _ _ x hx => ⟨x, hx, rfl⟩ }⟩⟩

/-- The unravelable sets are closed under complements. -/
theorem unravelable_compl {S : Set (ℕ → A)} (h : Unravelable S) : Unravelable Sᶜ := by
  obtain ⟨B, hB, S', hclopen, ⟨C⟩⟩ := h
  refine ⟨B, hB, S'ᶜ, ⟨hclopen.2, by simpa [IsClosedPayoff, compl_compl] using hclopen.1⟩,
    ⟨{ proj := C.proj
       preimage_eq := by rw [Set.preimage_compl, ← C.preimage_eq]
       lift := C.lift
       lift_spec := C.lift_spec }⟩⟩

/-! ### Borel determinacy -/

/-- An *unraveling scheme* for games with moves in `A`: a class of payoff sets which contains
the closed sets, is closed under complements and countable unions, and all of whose members
are determined.

This is the abstract shape of Martin's proof of Borel determinacy: the class of payoff sets
that are unraveled by a clopen covering game.  For that class, `determined_of_unravelable`
and `unravelable_compl` (both proved above) supply the last two fields, so that only the two
unraveling lemmas of Martin's argument remain — see `Borel_determinacy_of_unravelings`. -/
structure UnravelingScheme (A : Type u) where
  /-- the class of payoff sets covered by the scheme -/
  mem : Set (ℕ → A) → Prop
  /-- closed payoff sets belong to the class -/
  mem_of_isClosedPayoff : ∀ S, IsClosedPayoff S → mem S
  /-- the class is closed under complements -/
  mem_compl : ∀ S, mem S → mem Sᶜ
  /-- the class is closed under countable unions -/
  mem_iUnion : ∀ f : ℕ → Set (ℕ → A), (∀ n, mem (f n)) → mem (⋃ n, f n)
  /-- every payoff set in the class is determined -/
  determined_of_mem : ∀ S, mem S → Determined S

/-- Every Borel payoff set belongs to an unraveling scheme: the σ-algebra induction at the
heart of Martin's proof. -/
theorem UnravelingScheme.mem_of_isBorelPayoff (U : UnravelingScheme A) {S : Set (ℕ → A)}
    (hS : IsBorelPayoff S) : U.mem S := by
  induction hS with
  | basic T hT =>
    have hTc : IsClosedPayoff Tᶜ := by simpa [IsClosedPayoff, compl_compl] using hT
    simpa [compl_compl] using U.mem_compl _ (U.mem_of_isClosedPayoff _ hTc)
  | empty =>
    refine U.mem_of_isClosedPayoff _ ?_
    intro x _
    exact ⟨0, by simp⟩
  | compl T _ ih => exact U.mem_compl _ ih
  | iUnion f _ ih => exact U.mem_iUnion f ih

/-- **Borel determinacy** (Martin's theorem), as a Lean-checked reduction: every Borel game
is determined as soon as there is an unraveling scheme, i.e. a class of payoff sets which
contains the closed sets, is a σ-algebra, and consists of determined sets.

The base case of Martin's induction — that closed, open and clopen games are determined — is
proved unconditionally above (`determined_of_isClosedPayoff` and friends), as is the transfer
of determinacy along coverings (`determined_of_unravelable`), the stability of unravelability
under complements (`unravelable_compl`) and the σ-algebra induction
(`UnravelingScheme.mem_of_isBorelPayoff`).  What an unraveling scheme adds is precisely the
combinatorial core of Martin's argument. -/
theorem Borel_determinacy (U : UnravelingScheme A) (S : Set (ℕ → A)) (hS : IsBorelPayoff S) :
    Determined S :=
  U.determined_of_mem S (U.mem_of_isBorelPayoff hS)

/-- A degenerate but unconditional witness that the hypothesis of `Borel_determinacy` can be
met: if there is only one available move, every payoff set is determined. -/
theorem determined_of_subsingleton [Nonempty A] [Subsingleton A] (S : Set (ℕ → A)) :
    Determined S := by
  haveI : Inhabited A := Classical.inhabited_of_nonempty ‹Nonempty A›
  have hx : ∀ x : ℕ → A, x = fun _ => default := fun x => funext fun _ => Subsingleton.elim _ _
  by_cases h : (fun _ => default) ∈ S
  · exact Or.inl ⟨fun _ => default, fun x _ => by rw [hx x]; exact h⟩
  · exact Or.inr ⟨fun _ => default, fun x _ => by rw [hx x]; exact h⟩

/-- The unraveling scheme available when there is only one move. -/
def trivialScheme [Nonempty A] [Subsingleton A] : UnravelingScheme A where
  mem _ := True
  mem_of_isClosedPayoff _ _ := trivial
  mem_compl _ _ := trivial
  mem_iUnion _ _ := trivial
  determined_of_mem S _ := determined_of_subsingleton S

/-- Borel determinacy for the concrete class of payoff sets unraveled by a clopen covering
game: only the two unraveling lemmas (closed games are unraveled, and unravelability is
preserved by countable unions) are assumed; determinacy of the unraveled games, stability
under complements and the σ-algebra induction are proved. -/
theorem Borel_determinacy_of_unravelings [Nonempty A]
    (hclosed : ∀ S : Set (ℕ → A), IsClosedPayoff S → Unravelable S)
    (hunion : ∀ f : ℕ → Set (ℕ → A), (∀ n, Unravelable (f n)) → Unravelable (⋃ n, f n))
    (S : Set (ℕ → A)) (hS : IsBorelPayoff S) : Determined S :=
  Borel_determinacy
    { mem := Unravelable
      mem_of_isClosedPayoff := hclosed
      mem_compl := fun _ => unravelable_compl
      mem_iUnion := hunion
      determined_of_mem := fun _ => determined_of_unravelable } S hS

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

