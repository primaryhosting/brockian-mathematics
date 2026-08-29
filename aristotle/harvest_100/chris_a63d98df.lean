/-
/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
Every open game is determined (Gale–Stewart).

We consider the infinite two-player game on a nonempty set `A` of moves: the two players
alternately choose elements of `A`, player I moving at the even stages and player II at the odd
stages, producing a play `x : ℕ → A`.  Player I wins the play `x` iff `x ∈ W`, where `W` is the
payoff set.  A *strategy* is a function `List A → A` assigning a move to every position (finite
sequence of previous moves).

The theorem states: if `W` is open in the product topology on `ℕ → A` (with `A` discrete), then
either player I has a winning strategy or player II has one.
-/

namespace Frontier

open scoped Classical

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/
def pref (x : ℕ → A) (n : ℕ) : List A := (List.range n).map x

/-- Player I follows the strategy `σ` in the play `x`, from stage `p.length` on. -/
def IFollows (σ : List A → A) (p : List A) (x : ℕ → A) : Prop :=
  ∀ n, p.length ≤ n → Even n → x n = σ (pref x n)

/-- Player II follows the strategy `τ` in the play `x`, from stage `p.length` on. -/
def IIFollows (τ : List A → A) (p : List A) (x : ℕ → A) : Prop :=
  ∀ n, p.length ≤ n → ¬ Even n → x n = τ (pref x n)

/-- Player I has a winning strategy in the game with payoff set `W` started at position `p`. -/
def WinI (W : Set (ℕ → A)) (p : List A) : Prop :=
  ∃ σ : List A → A, ∀ x : ℕ → A, pref x p.length = p → IFollows σ p x → x ∈ W

/-- Combinatorial openness of a payoff set: every winning play has a finite prefix all of whose
extensions are winning. -/
def IsOpenPayoff (W : Set (ℕ → A)) : Prop :=
  ∀ x ∈ W, ∃ n, ∀ y : ℕ → A, (∀ i < n, y i = x i) → y ∈ W

/-! ### Basic facts about prefixes -/

@[simp] theorem pref_zero (x : ℕ → A) : pref x 0 = [] := rfl

@[simp] theorem length_pref (x : ℕ → A) (n : ℕ) : (pref x n).length = n := by
  simp [pref]

theorem pref_succ (x : ℕ → A) (n : ℕ) : pref x (n + 1) = pref x n ++ [x n] := by
  simp [pref, List.range_succ]

theorem getElem_pref (x : ℕ → A) {n i : ℕ} (h : i < n) :
    (pref x n)[i]'(by simpa using h) = x i := by
  simp [pref]

theorem pref_eq_iff {x y : ℕ → A} {n : ℕ} : pref x n = pref y n ↔ ∀ i < n, x i = y i := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simpa [pref, List.getElem?_map, List.getElem?_range, hi] using this
  · intro h
    simp only [pref]
    exact List.map_congr_left (by simpa using fun i hi => h i hi)

/-! ### Existence of plays -/

/-- The position after `n` moves when I plays `σ` and II plays `τ`. -/
def posn (σ τ : List A → A) : ℕ → List A
  | 0 => []
  | n + 1 => posn σ τ n ++ [if Even (posn σ τ n).length then σ (posn σ τ n) else τ (posn σ τ n)]

theorem length_posn (σ τ : List A → A) (n : ℕ) : (posn σ τ n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [posn, ih]

/-- For any pair of strategies there is a play in which both players follow them. -/
theorem exists_play (σ τ : List A → A) :
    ∃ x : ℕ → A, IFollows σ [] x ∧ IIFollows τ [] x := by
  set x : ℕ → A := fun n => if Even n then σ (posn σ τ n) else τ (posn σ τ n) with hxdef
  have key : ∀ n, pref x n = posn σ τ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pref_succ, ih]
      simp [posn, length_posn, hxdef]
  refine ⟨x, ?_, ?_⟩
  · intro n _ hn
    rw [key n, hxdef]
    simp [hn]
  · intro n _ hn
    rw [key n, hxdef]
    simp [hn]

/-- The two players cannot both have a winning strategy: the alternatives in the determinacy
statement are mutually exclusive (in particular neither of them holds vacuously). -/
theorem not_winning_both {W : Set (ℕ → A)} (σ τ : List A → A)
    (hσ : ∀ x : ℕ → A, IFollows σ [] x → x ∈ W)
    (hτ : ∀ x : ℕ → A, IIFollows τ [] x → x ∉ W) : False := by
  obtain ⟨x, hI, hII⟩ := exists_play σ τ
  exact hτ x hII (hσ x hI)

/-! ### The key combinatorial lemmas -/

/-- If player I wins from every one-move extension of the position `r`, he wins from `r`.
(This is used for positions `r` where it is player II's turn; the parity of `r.length` turns out
to be irrelevant.) -/
theorem winI_of_forall_snoc [Inhabited A] {W : Set (ℕ → A)} {r : List A}
    (h : ∀ b, WinI W (r ++ [b])) : WinI W r := by
  choose S hS using h
  refine ⟨fun r' => if hlt : r.length < r'.length then S (r'[r.length]'hlt) r' else default,
    fun x hx hfol => ?_⟩
  set b := x r.length with hb
  have hpref : pref x (r ++ [b]).length = r ++ [b] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx]
  refine hS b x hpref (fun n hn hne => ?_)
  have hlen : r.length + 1 ≤ n := by simpa using hn
  have hlt : r.length < (pref x n).length := by rw [length_pref]; omega
  have := hfol n (by omega) hne
  rw [this]
  simp only [dif_pos hlt, getElem_pref x (show r.length < n by omega)]
  rw [hb]

theorem winI_of_snoc {W : Set (ℕ → A)} {q : List A} {a : A}
    (heven : Even q.length) (h : WinI W (q ++ [a])) : WinI W q := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun r => if r = q then a else σ r, fun x hx hfol => ?_⟩
  have hmove : x q.length = a := by
    have := hfol q.length le_rfl heven
    simpa [hx] using this
  have hpref : pref x (q ++ [a]).length = q ++ [a] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx, hmove]
  refine hσ x hpref (fun n hn hne => ?_)
  have hlen : q.length + 1 ≤ n := by simpa using hn
  have hne' : pref x n ≠ q := by
    intro hcon
    have := congrArg List.length hcon
    simp at this
    omega
  have := hfol n (by omega) hne
  simpa [hne'] using this

/-! ### Determinacy -/

/-- **Gale–Stewart** for combinatorially open payoff sets. -/
theorem gale_stewart_openPayoff [Inhabited A] (W : Set (ℕ → A)) (hW : IsOpenPayoff W) :
    (∃ σ : List A → A, ∀ x : ℕ → A, IFollows σ [] x → x ∈ W) ∨
      (∃ τ : List A → A, ∀ x : ℕ → A, IIFollows τ [] x → x ∉ W) := by
  by_cases hwin : WinI W ([] : List A)
  · obtain ⟨σ, hσ⟩ := hwin
    exact Or.inl ⟨σ, fun x hfol => hσ x rfl hfol⟩
  · right
    have hstepI : ∀ q : List A, Even q.length → ¬ WinI W q → ∀ a, ¬ WinI W (q ++ [a]) :=
      fun q hq hnq a hcon => hnq (winI_of_snoc hq hcon)
    have hstepII : ∀ r : List A, ¬ WinI W r → ∃ b, ¬ WinI W (r ++ [b]) := by
      intro r hnr
      by_contra hc
      push_neg at hc
      exact hnr (winI_of_forall_snoc hc)
    refine ⟨fun r => if h : ∃ b, ¬ WinI W (r ++ [b]) then h.choose else default,
      fun x hfol hxW => ?_⟩
    have hpos : ∀ n, ¬ WinI W (pref x n) := by
      intro n
      induction n with
      | zero => simpa using hwin
      | succ n ih =>
        rw [pref_succ]
        by_cases hn : Even n
        · exact hstepI (pref x n) (by simpa using hn) ih (x n)
        · have hex := hstepII (pref x n) ih
          -- player II's move keeps the position non-winning for player I
          have hmove := hfol n (by simp) hn
          rw [hmove]
          simp only [dif_pos hex]
          exact hex.choose_spec
    obtain ⟨n, hn⟩ := hW x hxW
    refine hpos n ⟨fun _ => default, fun y hy _ => hn y ?_⟩
    rw [length_pref] at hy
    exact fun i hi => (pref_eq_iff.mp hy) i hi

theorem isOpenPayoff_of_isOpen [TopologicalSpace A] {W : Set (ℕ → A)} (hW : IsOpen W) :
    IsOpenPayoff W := by
  intro x hx
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW x hx
  refine ⟨(I.sup id) + 1, fun y hy => hsub ?_⟩
  intro i hi
  have : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [hy i (by omega)]
  exact (hu i hi).2

/-- **Gale–Stewart theorem**: every open game is determined.

`A` is the (nonempty) set of moves, `W ⊆ A^ℕ` the payoff set of player I, open in the product
topology of the discrete topology on `A`.  Then either player I has a strategy `σ` all of whose
plays lie in `W`, or player II has a strategy `τ` all of whose plays avoid `W`.

(The discreteness assumption is stated because it is part of the classical statement; the proof
only uses that `W` is open in the product topology.) -/
theorem Gale_Stewart_open [Inhabited A] [TopologicalSpace A] [DiscreteTopology A]
    (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : List A → A, ∀ x : ℕ → A, IFollows σ [] x → x ∈ W) ∨
      (∃ τ : List A → A, ∀ x : ℕ → A, IIFollows τ [] x → x ∉ W) :=
  gale_stewart_openPayoff W (isOpenPayoff_of_isOpen hW)

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

