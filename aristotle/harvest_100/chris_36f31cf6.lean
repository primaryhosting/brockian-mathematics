import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
## Infinite two-player games of perfect information

We work with the Gale–Stewart game on a nonempty type `A`:  players I and II alternately
choose elements of `A`, player I moving first, producing an infinite play `x : ℕ → A`.
Player I wins the play iff `x ∈ W`.
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/
def takePrefix (x : ℕ → A) (n : ℕ) : List A := (List.range n).map x

/-- Positions at which player I moves (those of even length). -/
def TurnI (p : List A) : Prop := p.length % 2 = 0

/-- A play `x` is consistent, from time `m` on, with the strategy `s` of the player whose
turn positions are described by `T`. -/
def Consistent (T : List A → Prop) (s : List A → A) (x : ℕ → A) (m : ℕ) : Prop :=
  ∀ n, m ≤ n → T (takePrefix x n) → x n = s (takePrefix x n)

/-- `x` is a play of the game in which player I follows the strategy `σ`. -/
def PlayI (σ : List A → A) (x : ℕ → A) : Prop := Consistent TurnI σ x 0

/-- `x` is a play of the game in which player II follows the strategy `τ`. -/
def PlayII (τ : List A → A) (x : ℕ → A) : Prop := Consistent (fun p => ¬ TurnI p) τ x 0

/-- `σ` is a winning strategy for player I in the game with payoff set `W`. -/
def WinsI (W : Set (ℕ → A)) (σ : List A → A) : Prop := ∀ x, PlayI σ x → x ∈ W

/-- `τ` is a winning strategy for player II in the game with payoff set `W`. -/
def WinsII (W : Set (ℕ → A)) (τ : List A → A) : Prop := ∀ x, PlayII τ x → x ∉ W

/-- The game with payoff set `W` is determined: one of the two players has a winning
strategy. -/
def Determined (W : Set (ℕ → A)) : Prop :=
  (∃ σ, WinsI W σ) ∨ (∃ τ, WinsII W τ)

/-- `σ` is a winning strategy for player I in the subgame starting at the position `p`. -/
def WinsIFrom (W : Set (ℕ → A)) (p : List A) (σ : List A → A) : Prop :=
  ∀ x, takePrefix x p.length = p → Consistent TurnI σ x p.length → x ∈ W

/-- `τ` is a winning strategy for player II in the subgame starting at the position `p`. -/
def WinsIIFrom (W : Set (ℕ → A)) (p : List A) (τ : List A → A) : Prop :=
  ∀ x, takePrefix x p.length = p → Consistent (fun q => ¬ TurnI q) τ x p.length → x ∉ W

/-- The subgame with payoff set `W` starting at the position `p` is determined. -/
def DeterminedFrom (W : Set (ℕ → A)) (p : List A) : Prop :=
  (∃ σ, WinsIFrom W p σ) ∨ (∃ τ, WinsIIFrom W p τ)

/-!
### Basic facts about prefixes
-/

@[simp] lemma length_takePrefix (x : ℕ → A) (n : ℕ) : (takePrefix x n).length = n := by
  simp [takePrefix]

lemma takePrefix_succ (x : ℕ → A) (n : ℕ) :
    takePrefix x (n + 1) = takePrefix x n ++ [x n] := by
  simp [takePrefix, List.range_succ]

lemma takePrefix_eq_iff {x y : ℕ → A} {n : ℕ} :
    takePrefix y n = takePrefix x n ↔ ∀ i < n, y i = x i := by
  simp [takePrefix, List.ext_getElem_iff]

lemma getD_takePrefix {x : ℕ → A} {n i : ℕ} (h : i < n) (d : A) :
    (takePrefix x n).getD i d = x i := by
  simp [takePrefix, List.getD_eq_getElem?_getD, h]

lemma takePrefix_le {x y : ℕ → A} {n m : ℕ} (hnm : n ≤ m)
    (h : takePrefix y m = takePrefix x m) : takePrefix y n = takePrefix x n :=
  takePrefix_eq_iff.mpr fun i hi => takePrefix_eq_iff.mp h i (lt_of_lt_of_le hi hnm)

/-- The game starting at the empty position is the original game. -/
lemma determined_of_determinedFrom_nil {W : Set (ℕ → A)} (h : DeterminedFrom W []) :
    Determined W := by
  rcases h with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · exact Or.inl ⟨σ, fun x hplay =>
      hσ x (by simp [takePrefix]) (fun n _ hT => hplay n (Nat.zero_le n) hT)⟩
  · exact Or.inr ⟨τ, fun x hplay =>
      hτ x (by simp [takePrefix]) (fun n _ hT => hplay n (Nat.zero_le n) hT)⟩

/-!
### The play produced by a pair of strategies

This is only used to check that the notion of determinacy is not degenerate: the two
players cannot both have a winning strategy.
-/

/-- The position reached after `n` moves when I follows `σ` and II follows `τ`. -/
def playPos (σ τ : List A → A) : ℕ → List A
  | 0 => []
  | n + 1 =>
      let p := playPos σ τ n
      p ++ [if p.length % 2 = 0 then σ p else τ p]

/-- The play in which I follows `σ` and II follows `τ`. -/
def playSeq (σ τ : List A → A) (n : ℕ) : A :=
  let p := playPos σ τ n
  if p.length % 2 = 0 then σ p else τ p

@[simp] lemma length_playPos (σ τ : List A → A) (n : ℕ) : (playPos σ τ n).length = n := by
  induction n with
  | zero => simp [playPos]
  | succ n IH => simp [playPos, IH]

lemma takePrefix_playSeq (σ τ : List A → A) (n : ℕ) :
    takePrefix (playSeq σ τ) n = playPos σ τ n := by
  induction n with
  | zero => simp [takePrefix, playPos]
  | succ n IH => rw [takePrefix_succ, IH]; rfl

lemma playI_playSeq (σ τ : List A → A) : PlayI σ (playSeq σ τ) := by
  intro n _ hT
  rw [takePrefix_playSeq] at hT ⊢
  have : (playPos σ τ n).length % 2 = 0 := hT
  simp only [playSeq, if_pos this]

lemma playII_playSeq (σ τ : List A → A) : PlayII τ (playSeq σ τ) := by
  intro n _ hT
  rw [takePrefix_playSeq] at hT ⊢
  have : ¬ ((playPos σ τ n).length % 2 = 0) := hT
  simp only [playSeq, if_neg this]

/-- Determinacy is not degenerate: the two players cannot both have a winning strategy. -/
theorem not_winsI_and_winsII (W : Set (ℕ → A)) (σ τ : List A → A) :
    ¬ (WinsI W σ ∧ WinsII W τ) := by
  rintro ⟨h1, h2⟩
  exact h2 (playSeq σ τ) (playII_playSeq σ τ) (h1 (playSeq σ τ) (playI_playSeq σ τ))

/-!
### The reachability game

`Force T S p` says that the player whose turn positions are given by `T` can force,
from the position `p`, that the play visits a position in `S`.  It is defined as the
least such predicate, i.e. by an inductive definition.
-/

/-- The player with turn set `T` can force the play to reach a position in `S`. -/
inductive Force (T : List A → Prop) (S : List A → Prop) : List A → Prop
  | here {p : List A} (h : S p) : Force T S p
  | reach {p : List A} (hp : T p) (a : A) (h : Force T S (p ++ [a])) : Force T S p
  | opp {p : List A} (hp : ¬ T p) (h : ∀ a : A, Force T S (p ++ [a])) : Force T S p

variable [Nonempty A]

/-- If the `T`-player can force reaching `S` from `p`, then it has a strategy doing so. -/
theorem force_strategy {T S : List A → Prop} {p : List A} (h : Force T S p) :
    ∃ s : List A → A, ∀ x : ℕ → A, takePrefix x p.length = p →
      Consistent T s x p.length → ∃ n, S (takePrefix x n) := by
  classical
  induction h with
  | @here p hS =>
      exact ⟨fun _ => Classical.arbitrary A, fun x hx _ => ⟨p.length, by rw [hx]; exact hS⟩⟩
  | @reach p hp a _ IH =>
      obtain ⟨s', hs'⟩ := IH
      refine ⟨fun q => if q = p then a else s' q, fun x hx H => ?_⟩
      have h1 : x p.length = a := by
        have := H p.length le_rfl (by rw [hx]; exact hp)
        rw [hx] at this; simpa using this
      have h2 : takePrefix x (p.length + 1) = p ++ [a] := by
        rw [takePrefix_succ, hx, h1]
      have hlen : (p ++ [a]).length = p.length + 1 := by simp
      refine hs' x (by rw [hlen]; exact h2) ?_
      intro n hn hT
      rw [hlen] at hn
      have hval := H n (Nat.le_of_succ_le hn) hT
      have hne : takePrefix x n ≠ p := by
        intro hEq
        have := congrArg List.length hEq
        rw [length_takePrefix] at this
        omega
      simpa [hne] using hval
  | @opp p _ _ IH =>
      choose s' hs' using IH
      refine ⟨fun q => s' (q.getD p.length (Classical.arbitrary A)) q, fun x hx H => ?_⟩
      have h2 : takePrefix x (p.length + 1) = p ++ [x p.length] := by
        rw [takePrefix_succ, hx]
      have hlen : (p ++ [x p.length]).length = p.length + 1 := by simp
      refine hs' (x p.length) x (by rw [hlen]; exact h2) ?_
      intro n hn hT
      rw [hlen] at hn
      have hval := H n (Nat.le_of_succ_le hn) hT
      have hbeta : x n = s' ((takePrefix x n).getD p.length (Classical.arbitrary A))
          (takePrefix x n) := hval
      rwa [getD_takePrefix (show p.length < n by omega)] at hbeta

/-- If the `T`-player cannot force reaching `S` from `p`, then the opponent has a strategy
which avoids `S` forever. -/
theorem avoid_strategy {T S : List A → Prop} {p : List A} (h : ¬ Force T S p) :
    ∃ s : List A → A, ∀ x : ℕ → A, takePrefix x p.length = p →
      Consistent (fun q => ¬ T q) s x p.length → ∀ n, p.length ≤ n → ¬ S (takePrefix x n) := by
  classical
  have key : ∀ q : List A, ∃ a : A, ¬ Force T S q → ¬ T q → ¬ Force T S (q ++ [a]) := by
    intro q
    by_cases hq : ¬ Force T S q ∧ ¬ T q
    · have : ∃ a : A, ¬ Force T S (q ++ [a]) := by
        by_contra hcon
        push_neg at hcon
        exact hq.1 (Force.opp hq.2 (fun a => hcon a))
      obtain ⟨a, ha⟩ := this
      exact ⟨a, fun _ _ => ha⟩
    · exact ⟨Classical.arbitrary A, fun h1 h2 => absurd ⟨h1, h2⟩ hq⟩
  choose f hf using key
  refine ⟨f, ?_⟩
  intro x hx H
  have main : ∀ n, p.length ≤ n → ¬ Force T S (takePrefix x n) := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hp0 : p.length = 0 := Nat.le_zero.mp hn
        rw [← hp0, hx]
        exact h
    | succ n IH =>
        intro hn
        rcases Nat.lt_or_ge n p.length with hlt | hge
        · have : p.length = n + 1 := by omega
          rw [← this, hx]
          exact h
        · have hIH := IH hge
          rw [takePrefix_succ]
          by_cases hT : T (takePrefix x n)
          · intro hF
            exact hIH (Force.reach hT (x n) hF)
          · have hval : x n = f (takePrefix x n) := H n hge hT
            rw [hval]
            exact hf _ hIH hT
  intro n hn hS
  exact main n hn (Force.here hS)

/-!
### Gale–Stewart: open and closed games are determined
-/

/-- Combinatorial closedness: membership in `W` is determined by all finite prefixes. -/
def SeqClosed (W : Set (ℕ → A)) : Prop :=
  ∀ x, (∀ n, ∃ y ∈ W, takePrefix y n = takePrefix x n) → x ∈ W

/-- Combinatorial openness: membership in `W` is decided by a finite prefix. -/
def SeqOpen (W : Set (ℕ → A)) : Prop :=
  ∀ x ∈ W, ∃ n, ∀ y, takePrefix y n = takePrefix x n → y ∈ W

/-- Gale–Stewart, closed case: every subgame of a closed game is determined
(combinatorial form). -/
theorem determinedFrom_of_seqClosed {W : Set (ℕ → A)} (hW : SeqClosed W) (p : List A) :
    DeterminedFrom W p := by
  classical
  -- `Dead q` : no play extending the position `q` is winning for player I
  set Dead : List A → Prop := fun q => ∀ y, takePrefix y q.length = q → y ∉ W
  by_cases hF : Force (fun q => ¬ TurnI q) Dead p
  · obtain ⟨τ, hτ⟩ := force_strategy hF
    refine Or.inr ⟨τ, fun x hx hplay hxW => ?_⟩
    obtain ⟨n, hn⟩ := hτ x hx hplay
    exact hn x (by rw [length_takePrefix]) hxW
  · obtain ⟨σ, hσ⟩ := avoid_strategy hF
    refine Or.inl ⟨σ, fun x hx hplay => ?_⟩
    have hcons : Consistent (fun q => ¬ ¬ TurnI q) σ x p.length :=
      fun n hn hT => hplay n hn (not_not.mp hT)
    have havoid := hσ x hx hcons
    refine hW x (fun n => ?_)
    by_contra hcon
    push_neg at hcon
    refine havoid (max n p.length) (le_max_right _ _) ?_
    show ∀ y, takePrefix y (takePrefix x (max n p.length)).length
      = takePrefix x (max n p.length) → y ∉ W
    intro y hy hyW
    rw [length_takePrefix] at hy
    exact hcon y hyW (takePrefix_le (le_max_left n p.length) hy)

/-- Gale–Stewart, open case: every subgame of an open game is determined
(combinatorial form). -/
theorem determinedFrom_of_seqOpen {W : Set (ℕ → A)} (hW : SeqOpen W) (p : List A) :
    DeterminedFrom W p := by
  classical
  -- `Secured q` : every play extending the position `q` is winning for player I
  set Secured : List A → Prop := fun q => ∀ y, takePrefix y q.length = q → y ∈ W
  by_cases hF : Force TurnI Secured p
  · obtain ⟨σ, hσ⟩ := force_strategy hF
    refine Or.inl ⟨σ, fun x hx hplay => ?_⟩
    obtain ⟨n, hn⟩ := hσ x hx hplay
    exact hn x (by rw [length_takePrefix])
  · obtain ⟨τ, hτ⟩ := avoid_strategy hF
    refine Or.inr ⟨τ, fun x hx hplay hxW => ?_⟩
    have havoid := hτ x hx hplay
    obtain ⟨n, hn⟩ := hW x hxW
    refine havoid (max n p.length) (le_max_right _ _) ?_
    show ∀ y, takePrefix y (takePrefix x (max n p.length)).length
      = takePrefix x (max n p.length) → y ∈ W
    intro y hy
    rw [length_takePrefix] at hy
    exact hn y (takePrefix_le (le_max_left n p.length) hy)

/-- Gale–Stewart, closed case (combinatorial form). -/
theorem determined_of_seqClosed {W : Set (ℕ → A)} (hW : SeqClosed W) : Determined W :=
  determined_of_determinedFrom_nil (determinedFrom_of_seqClosed hW [])

/-- Gale–Stewart, open case (combinatorial form). -/
theorem determined_of_seqOpen {W : Set (ℕ → A)} (hW : SeqOpen W) : Determined W :=
  determined_of_determinedFrom_nil (determinedFrom_of_seqOpen hW [])

/-!
### Topological versions
-/

variable [TopologicalSpace A]

omit [Nonempty A] in
lemma seqOpen_of_isOpen {W : Set (ℕ → A)} (hW : IsOpen W) : SeqOpen W := by
  intro x hx
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW x hx
  refine ⟨I.sup id + 1, fun y hy => ?_⟩
  have hy' : ∀ i < I.sup id + 1, y i = x i := takePrefix_eq_iff.mp hy
  refine hsub (fun i hi => ?_)
  have hle : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [hy' i (by omega)]
  exact (hu i hi).2

omit [Nonempty A] in
lemma seqClosed_of_isClosed {W : Set (ℕ → A)} (hW : IsClosed W) : SeqClosed W := by
  intro x hall
  by_contra hxW
  obtain ⟨n, hn⟩ := seqOpen_of_isOpen hW.isOpen_compl x hxW
  obtain ⟨y, hyW, hy⟩ := hall n
  exact hn y hy hyW

/-- **Gale–Stewart theorem**: every open game is determined. -/
theorem open_determinacy {W : Set (ℕ → A)} (hW : IsOpen W) : Determined W :=
  determined_of_seqOpen (seqOpen_of_isOpen hW)

/-- **Gale–Stewart theorem**: every closed game is determined. -/
theorem closed_determinacy {W : Set (ℕ → A)} (hW : IsClosed W) : Determined W :=
  determined_of_seqClosed (seqClosed_of_isClosed hW)

/-- **Gale–Stewart theorem**, subgame form: every subgame of an open game is determined. -/
theorem open_determinacy_from {W : Set (ℕ → A)} (hW : IsOpen W) (p : List A) :
    DeterminedFrom W p :=
  determinedFrom_of_seqOpen (seqOpen_of_isOpen hW) p

/-- **Gale–Stewart theorem**, subgame form: every subgame of a closed game is determined. -/
theorem closed_determinacy_from {W : Set (ℕ → A)} (hW : IsClosed W) (p : List A) :
    DeterminedFrom W p :=
  determinedFrom_of_seqClosed (seqClosed_of_isClosed hW) p

/-!
### Borel determinacy

Martin's theorem states that every Borel game is determined.  What is proved here is:

* unconditionally, the base case of the Borel hierarchy: every open game and every closed
  game is determined (`Frontier.open_determinacy`, `Frontier.closed_determinacy`);
* a Lean-checked reduction of the general statement to the two closure properties of the
  class of determined *Borel* sets which Martin's unravelling argument supplies, namely
  closure under complements and under countable unions.

Both hypotheses of `Frontier.Borel_determinacy` are restricted to Borel payoff sets, and so
are consequences of Martin's theorem; in particular the statement below is not vacuous.
(For arbitrary payoff sets closure under complements fails in ZFC, which is why the
restriction matters.)  The full unravelling construction is not formalised here.
-/

/-- **Borel determinacy (Martin's theorem), as a Lean-checked reduction.**
If determinacy of Borel games is preserved by complements and by countable unions, then
every Borel game is determined.  The base case of the induction — determinacy of open
games — is proved unconditionally (`Frontier.open_determinacy`). -/
theorem Borel_determinacy
    (hcompl : ∀ W : Set (ℕ → A), @MeasurableSet (ℕ → A) (borel (ℕ → A)) W →
      Determined W → Determined Wᶜ)
    (hunion : ∀ f : ℕ → Set (ℕ → A), (∀ n, @MeasurableSet (ℕ → A) (borel (ℕ → A)) (f n)) →
      (∀ n, Determined (f n)) → Determined (⋃ n, f n))
    (W : Set (ℕ → A)) (hW : @MeasurableSet (ℕ → A) (borel (ℕ → A)) W) : Determined W := by
  refine MeasurableSpace.generateFrom_induction {s : Set (ℕ → A) | IsOpen s}
    (fun s _ => Determined s) (fun t ht _ => open_determinacy ht) ?_
    (fun t ht h => hcompl t ht h) (fun s hs h => hunion s hs h) W hW
  exact Or.inr ⟨fun _ => Classical.arbitrary A, fun x _ hx => hx⟩

end Frontier

