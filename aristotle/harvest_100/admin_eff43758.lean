/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GaleStewart

universe u

variable {X : Type u}

/-- The list of the first `n` moves of the play `a`. -/
def hist (a : ℕ → X) : ℕ → List X
  | 0 => []
  | n + 1 => hist a n ++ [a n]

@[simp] lemma hist_zero (a : ℕ → X) : hist a 0 = [] := rfl

@[simp] lemma hist_succ (a : ℕ → X) (n : ℕ) : hist a (n + 1) = hist a n ++ [a n] := rfl

@[simp] lemma hist_length (a : ℕ → X) (n : ℕ) : (hist a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [hist, ih]

lemma hist_getElem? (a : ℕ → X) : ∀ n i, i < n → (hist a n)[i]? = some (a i) := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · rw [hist_succ, List.getElem?_append_left (by simpa using h)]
      exact ih i h
    · subst h
      rw [hist_succ, List.getElem?_append_right (by simp)]
      simp

lemma hist_getD (a : ℕ → X) (d : X) {n i : ℕ} (hi : i < n) : (hist a n).getD i d = a i := by
  rw [List.getD_eq_getElem?_getD, hist_getElem? a n i hi]
  rfl

/-- Two plays with the same history of length `n` agree below `n`. -/
lemma eq_of_hist_eq {a b : ℕ → X} {n : ℕ} (h : hist a n = hist b n) :
    ∀ i < n, a i = b i := by
  intro i hi
  have := hist_getElem? a n i hi
  have hb := hist_getElem? b n i hi
  rw [h, hb] at this
  exact (Option.some_injective _ this).symm

/-- An open set of plays is determined by finite initial segments. -/
lemma isOpen_forcing [TopologicalSpace X] {A : Set (ℕ → X)} (hA : IsOpen A) {a : ℕ → X}
    (ha : a ∈ A) : ∃ n, ∀ b : ℕ → X, (∀ i < n, b i = a i) → b ∈ A := by
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hA a ha
  refine ⟨I.sup id + 1, fun b hb => hsub ?_⟩
  intro i hi
  have hile : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [hb i (by omega)]
  exact (hu i hi).2

section Strategies

/-- A play `a` follows the strategy `σ` for player I (who moves at even times). -/
def FollowsI (σ : List X → X) (a : ℕ → X) : Prop := ∀ n, Even n → a n = σ (hist a n)

/-- A play `a` follows the strategy `τ` for player II (who moves at odd times). -/
def FollowsII (τ : List X → X) (a : ℕ → X) : Prop := ∀ n, Odd n → a n = τ (hist a n)

/-- The position after `n` moves when both players follow their strategies. -/
def playPos (σ τ : List X → X) : ℕ → List X
  | 0 => []
  | n + 1 => playPos σ τ n ++ [if Even n then σ (playPos σ τ n) else τ (playPos σ τ n)]

/-- The play resulting from `σ` and `τ`. -/
def playSeq (σ τ : List X → X) (n : ℕ) : X :=
  if Even n then σ (playPos σ τ n) else τ (playPos σ τ n)

lemma hist_playSeq (σ τ : List X → X) (n : ℕ) : hist (playSeq σ τ) n = playPos σ τ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [hist, playPos, ih, playSeq]

/-- Any pair of strategies produces a play following both. -/
lemma exists_play (σ τ : List X → X) :
    ∃ a : ℕ → X, FollowsI σ a ∧ FollowsII τ a := by
  refine ⟨playSeq σ τ, ?_, ?_⟩
  · intro n hn
    rw [hist_playSeq]
    simp [playSeq, hn]
  · intro n hn
    rw [hist_playSeq]
    have : ¬ Even n := Nat.not_even_iff_odd.mpr hn
    simp [playSeq, this]

end Strategies

section Win

/-- The (data-valued) derivation that player I can force reaching `W` from position `p`. -/
inductive WinT (W : Set (List X)) : List X → Type u
  | base {p : List X} : p ∈ W → WinT W p
  | moveI {p : List X} (x : X) : Even p.length → WinT W (p ++ [x]) → WinT W p
  | moveII {p : List X} : Odd p.length → (∀ x : X, WinT W (p ++ [x])) → WinT W p

end Win

variable [Nonempty X]

/-- From a derivation that I can force `W` from `p`, one extracts a strategy for I. -/
theorem winT_strategy {W : Set (List X)} :
    ∀ {p : List X}, WinT W p → ∃ σ : List X → X,
      ∀ a : ℕ → X, hist a p.length = p →
        (∀ n, p.length ≤ n → Even n → a n = σ (hist a n)) → ∃ m, hist a m ∈ W := by
  classical
  intro p t
  induction t with
  | @base p hp =>
      refine ⟨fun _ => Classical.arbitrary X, fun a ha _ => ⟨p.length, ?_⟩⟩
      rw [ha]; exact hp
  | @moveI p x hev t ih =>
      obtain ⟨σ', hσ'⟩ := ih
      refine ⟨fun q => if q.length = p.length then x else σ' q, fun a ha hfollow => ?_⟩
      have hx : a p.length = x := by
        have := hfollow p.length le_rfl hev
        rw [this, ha]
        simp
      have hnext : hist a (p ++ [x]).length = p ++ [x] := by
        have : (p ++ [x]).length = p.length + 1 := by simp
        rw [this, hist_succ, ha, hx]
      refine hσ' a hnext ?_
      intro n hn hne
      have hlen : (p ++ [x]).length = p.length + 1 := by simp
      rw [hlen] at hn
      have h1 : a n = (fun q => if q.length = p.length then x else σ' q) (hist a n) :=
        hfollow n (by omega) hne
      rw [h1]
      have hne2 : (hist a n).length ≠ p.length := by simp; omega
      simp only [hne2, if_false]
  | @moveII p hodd f ih =>
      choose g hg using ih
      refine ⟨fun q => g (q.getD p.length (Classical.arbitrary X)) q, fun a ha hfollow => ?_⟩
      set x := a p.length
      have hnext : hist a (p ++ [x]).length = p ++ [x] := by
        have : (p ++ [x]).length = p.length + 1 := by simp
        rw [this, hist_succ, ha]
      refine hg x a hnext ?_
      intro n hn hne
      have hlen : (p ++ [x]).length = p.length + 1 := by simp
      rw [hlen] at hn
      have h1 : a n = g ((hist a n).getD p.length (Classical.arbitrary X)) (hist a n) :=
        hfollow n (by omega) hne
      rw [h1, hist_getD a _ (show p.length < n by omega)]

/-- If player I has no derivation from the empty position, then player II has a strategy
keeping the play out of `W` forever. -/
theorem no_winT_strategy {W : Set (List X)} (h : IsEmpty (WinT W ([] : List X))) :
    ∃ τ : List X → X, ∀ a : ℕ → X, FollowsII τ a → ∀ m, hist a m ∉ W := by
  classical
  have hnotW : ∀ q : List X, IsEmpty (WinT W q) → q ∉ W := fun q hq hqW => hq.false (WinT.base hqW)
  have heven : ∀ q : List X, Even q.length → IsEmpty (WinT W q) →
      ∀ x, IsEmpty (WinT W (q ++ [x])) := by
    intro q hq hnd x
    exact ⟨fun t => hnd.false (WinT.moveI x hq t)⟩
  have hodd : ∀ q : List X, Odd q.length → IsEmpty (WinT W q) →
      ∃ x, IsEmpty (WinT W (q ++ [x])) := by
    intro q hq hnd
    by_contra hcon
    push_neg at hcon
    have hne : ∀ x, Nonempty (WinT W (q ++ [x])) := hcon
    exact hnd.false (WinT.moveII hq (fun x => Classical.choice (hne x)))
  refine ⟨fun q => if hq : ∃ x, IsEmpty (WinT W (q ++ [x])) then hq.choose
    else Classical.arbitrary X, fun a ha m => ?_⟩
  have key : ∀ m, IsEmpty (WinT W (hist a m)) := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih =>
        rcases Nat.even_or_odd m with hm | hm
        · have := heven (hist a m) (by simpa using hm) ih (a m)
          simpa using this
        · have hex : ∃ x, IsEmpty (WinT W (hist a m ++ [x])) :=
            hodd (hist a m) (by simpa using hm) ih
          have ham : a m = hex.choose := by
            rw [ha m hm]
            simp [hex]
          rw [hist_succ, ham]
          exact hex.choose_spec
  exact hnotW _ (key m)

end GaleStewart

namespace Frontier

open GaleStewart

/-- **Gale–Stewart**: every open game is determined.  The moves are elements of a nonempty
discrete space `X`; a play is a sequence `a : ℕ → X`, player I choosing `a 0, a 2, …` and
player II choosing `a 1, a 3, …`.  Player I wins the play iff `a ∈ A`.  If the payoff set `A`
is open in the product topology, then one of the players has a winning strategy.

(The discreteness hypothesis is part of the usual statement; the proof below in fact only uses
that `A` is open in the product topology of whatever topology `X` carries.) -/
theorem Gale_Stewart_open {X : Type u} [Nonempty X] [TopologicalSpace X] [DiscreteTopology X]
    (A : Set (ℕ → X)) (hA : IsOpen A) :
    (∃ σ : List X → X, ∀ a : ℕ → X, FollowsI σ a → a ∈ A) ∨
      (∃ τ : List X → X, ∀ a : ℕ → X, FollowsII τ a → a ∉ A) := by
  -- `W` is the set of finite positions that already force a win for player I
  set W : Set (List X) := {p : List X | ∀ b : ℕ → X, hist b p.length = p → b ∈ A} with hW
  have hWA : ∀ (a : ℕ → X) (m : ℕ), hist a m ∈ W → a ∈ A := by
    intro a m hm
    exact hm a (by simp)
  have hAW : ∀ a : ℕ → X, a ∈ A → ∃ m, hist a m ∈ W := by
    intro a ha
    obtain ⟨n, hn⟩ := isOpen_forcing hA ha
    refine ⟨n, fun b hb => hn b ?_⟩
    intro i hi
    exact eq_of_hist_eq (by simpa using hb) i hi
  rcases isEmpty_or_nonempty (WinT W ([] : List X)) with hE | hne
  · right
    obtain ⟨τ, hτ⟩ := no_winT_strategy hE
    refine ⟨τ, ?_⟩
    intro a ha haA
    obtain ⟨m, hm⟩ := hAW a haA
    exact hτ a ha m hm
  · left
    obtain ⟨t⟩ := hne
    obtain ⟨σ, hσ⟩ := winT_strategy t
    refine ⟨σ, fun a ha => ?_⟩
    obtain ⟨m, hm⟩ := hσ a (by simp) (fun n _ hn => ha n hn)
    exact hWA a m hm

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

