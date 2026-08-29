import Mathlib
import RequestProject.GaleStewartOpen

/-!
# Gale–Stewart for topologically open payoff sets

`Frontier.Gale_Stewart_open` states openness of the payoff set combinatorially (membership of a
play is guaranteed by a finite initial segment of it).  Here we record the corollary phrased with
Mathlib's product topology on `ℕ → A`.
-/

namespace Frontier

universe u

variable {A : Type u}

/-- **Gale–Stewart theorem**, topological form: if the payoff set `W` is open in the product
topology on `ℕ → A` (for instance, the product of discrete topologies), then the associated
infinite game is determined. -/
theorem gale_stewart_isOpen [Nonempty A] [TopologicalSpace A] (W : Set (ℕ → A))
    (hW : IsOpen W) :
    (∃ σ : List A → A, ∀ τ : List A → A, playSeq σ τ ∈ W) ∨
      (∃ τ : List A → A, ∀ σ : List A → A, playSeq σ τ ∉ W) := by
  refine Gale_Stewart_open (fun x => x ∈ W) ?_
  intro x hx
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hW x hx
  refine ⟨I.sup id + 1, fun y hy => ?_⟩
  refine hsub fun i hi => ?_
  have hle : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [hy i (by omega)]
  exact (hu i hi).2

end Frontier

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

variable {A : Type u}

/-- The move dictated at position `s` by the pair of strategies `(σ, τ)`:
player I (playing `σ`) moves at positions of even length, player II (playing `τ`)
moves at positions of odd length. -/
def nextMove (σ τ : List A → A) (s : List A) : A :=
  if s.length % 2 = 0 then σ s else τ s

/-- `hist σ τ s n` is the position reached after `n` further moves, starting from
the position `s`, when the players follow the strategies `σ` and `τ`. -/
def hist (σ τ : List A → A) : List A → Nat → List A
  | s, 0 => s
  | s, (n + 1) => hist σ τ (s ++ [nextMove σ τ s]) n

/-- The infinite play resulting from the strategies `σ` (player I) and `τ` (player II). -/
def playSeq (σ τ : List A → A) (n : Nat) : A := nextMove σ τ (hist σ τ [] n)

/-- The list of the first `n` values of the sequence `x`. -/
def pre (x : Nat → A) (n : Nat) : List A := (List.range n).map x

theorem pre_length (x : Nat → A) (n : Nat) : (pre x n).length = n := by
  simp [pre]

theorem pre_getElem (x : Nat → A) (n i : Nat) (h : i < (pre x n).length) :
    (pre x n)[i] = x i := by
  simp [pre]

theorem pre_succ (x : Nat → A) (n : Nat) : pre x (n + 1) = pre x n ++ [x n] := by
  simp [pre, List.range_succ]

theorem hist_succ (σ τ : List A → A) (s : List A) (n : Nat) :
    hist σ τ s (n + 1) = hist σ τ s n ++ [nextMove σ τ (hist σ τ s n)] := by
  induction n generalizing s with
  | zero => simp [hist]
  | succ n ih => simpa [hist] using ih (s ++ [nextMove σ τ s])

theorem hist_nil_eq_pre (σ τ : List A → A) (n : Nat) :
    hist σ τ [] n = pre (playSeq σ τ) n := by
  induction n with
  | zero => simp [hist, pre]
  | succ n ih => rw [hist_succ, ih, pre_succ, playSeq, ih]

/-- `WinBy S σ s` says that, from position `s`, when player I follows the strategy `σ`,
play is forced into the set `S` of positions after finitely many moves. -/
inductive WinBy (S : List A → Prop) (σ : List A → A) : List A → Prop
  | base {s : List A} : S s → WinBy S σ s
  | move_I {s : List A} : s.length % 2 = 0 → WinBy S σ (s ++ [σ s]) → WinBy S σ s
  | move_II {s : List A} : ¬ s.length % 2 = 0 → (∀ a : A, WinBy S σ (s ++ [a])) → WinBy S σ s

/-- `WinBy S σ s` only depends on the values of `σ` at positions extending `s`. -/
theorem winBy_congr {S : List A → Prop} {σ : List A → A} {s : List A} (h : WinBy S σ s)
    (σ' : List A → A) (hagree : ∀ u, s <+: u → σ u = σ' u) : WinBy S σ' s := by
  revert hagree
  induction h with
  | @base s hs => exact fun _ => WinBy.base hs
  | @move_I s hlen _ ih =>
      intro hag
      refine WinBy.move_I hlen ?_
      rw [← hag s (List.prefix_refl s)]
      exact ih fun u hu => hag u ((List.prefix_append s [σ s]).trans hu)
  | @move_II s hlen _ ih =>
      intro hag
      exact WinBy.move_II hlen fun a =>
        ih a fun u hu => hag u ((List.prefix_append s [a]).trans hu)

/-- Following a winning strategy, player I really does reach `S`. -/
theorem winBy_reaches {S : List A → Prop} {σ : List A → A} {s : List A} (h : WinBy S σ s) :
    ∀ τ : List A → A, ∃ n, S (hist σ τ s n) := by
  induction h with
  | @base s hs => exact fun _ => ⟨0, hs⟩
  | @move_I s hlen _ ih =>
      intro τ
      obtain ⟨n, hn⟩ := ih τ
      exact ⟨n + 1, by simpa [hist, nextMove, hlen] using hn⟩
  | @move_II s hlen _ ih =>
      intro τ
      obtain ⟨n, hn⟩ := ih (τ s) τ
      exact ⟨n + 1, by simpa [hist, nextMove, hlen] using hn⟩

/-- Player I has a strategy that forces the play into `S` in finitely many moves,
starting from position `s`. -/
def IWinQ (S : List A → Prop) (s : List A) : Prop := ∃ σ : List A → A, WinBy S σ s

theorem iwinq_of_move_I {S : List A → Prop} {s : List A} (hs : s.length % 2 = 0) {a : A}
    (h : IWinQ S (s ++ [a])) : IWinQ S s := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun u => if u.length = s.length then a else σ u, ?_⟩
  have hw : WinBy S (fun u => if u.length = s.length then a else σ u) (s ++ [a]) := by
    refine winBy_congr hσ _ ?_
    intro u hu
    have hlen : s.length + 1 ≤ u.length := by
      have := hu.length_le
      simpa using this
    have : ¬ u.length = s.length := by omega
    simp [this]
  refine WinBy.move_I hs ?_
  simpa using hw

theorem iwinq_of_move_II [Nonempty A] {S : List A → Prop} {s : List A} (hs : ¬ s.length % 2 = 0)
    (h : ∀ a : A, IWinQ S (s ++ [a])) : IWinQ S s := by
  have hF : ∀ a, WinBy S (Classical.choose (h a)) (s ++ [a]) := fun a => Classical.choose_spec (h a)
  refine ⟨fun u => if hlt : s.length < u.length then Classical.choose (h (u[s.length]'hlt)) u
    else Classical.choice inferInstance, ?_⟩
  refine WinBy.move_II hs fun a => ?_
  refine winBy_congr (hF a) _ ?_
  intro u hu
  have hlen : s.length + 1 ≤ u.length := by
    have := hu.length_le
    simpa using this
  have hlt : s.length < u.length := hlen
  have hidx : u[s.length]'hlt = a := by
    have hb : s.length < (s ++ [a]).length := by simp
    have := hu.getElem hb
    rw [← this]
    rw [List.getElem_append_right (Nat.le_refl s.length)]
    simp
  rw [dif_pos hlt, hidx]

/-- **Gale–Stewart theorem for open games.**  Two players alternately choose elements of a
nonempty set `A` of moves (player I choosing `x 0, x 2, …`, player II choosing `x 1, x 3, …`),
producing an infinite play `x : Nat → A`; player I wins iff `W x`.  Strategies are functions
from the current position (the list of moves played so far) to the next move.  If the payoff
set `W` is open — i.e. membership of any of its elements is already guaranteed by a finite
initial segment of it — then the game is determined: one of the two players has a winning
strategy. -/
theorem Gale_Stewart_open [Nonempty A] (W : (Nat → A) → Prop)
    (hopen : ∀ x, W x → ∃ n : Nat, ∀ y : Nat → A, (∀ i < n, y i = x i) → W y) :
    (∃ σ : List A → A, ∀ τ : List A → A, W (playSeq σ τ)) ∨
      (∃ τ : List A → A, ∀ σ : List A → A, ¬ W (playSeq σ τ)) := by
  -- `S s` says that the finite position `s` already guarantees a win for player I.
  obtain ⟨S, hW1, hW2⟩ : ∃ S : List A → Prop,
      (∀ x : Nat → A, W x → ∃ n, S (pre x n)) ∧ (∀ (x : Nat → A) (n : Nat), S (pre x n) → W x) := by
    refine ⟨fun s => ∀ y : Nat → A, (∀ i (hi : i < s.length), y i = s[i]) → W y, ?_, ?_⟩
    · intro x hx
      obtain ⟨n, hn⟩ := hopen x hx
      refine ⟨n, fun y hy => hn y fun i hi => ?_⟩
      have hi' : i < (pre x n).length := by rw [pre_length]; exact hi
      have := hy i hi'
      rwa [pre_getElem] at this
    · intro x n hn
      exact hn x fun i hi => (pre_getElem x n i hi).symm
  by_cases hI : IWinQ S []
  · -- Player I has a winning strategy.
    left
    obtain ⟨σ, hσ⟩ := hI
    refine ⟨σ, fun τ => ?_⟩
    obtain ⟨n, hn⟩ := winBy_reaches hσ τ
    rw [hist_nil_eq_pre] at hn
    exact hW2 _ n hn
  · -- Otherwise player II can keep the position out of player I's winning region.
    right
    have hpoint : ∀ u : List A, ∃ a : A,
        (∃ b : A, ¬ IWinQ S (u ++ [b])) → ¬ IWinQ S (u ++ [a]) := by
      intro u
      cases Classical.em (∃ b : A, ¬ IWinQ S (u ++ [b])) with
      | inl hb => exact ⟨Classical.choose hb, fun _ => Classical.choose_spec hb⟩
      | inr hb => exact ⟨Classical.choice inferInstance, fun hc => absurd hc hb⟩
    obtain ⟨τ, hτ⟩ : ∃ τ : List A → A,
        ∀ u : List A, (∃ a : A, ¬ IWinQ S (u ++ [a])) → ¬ IWinQ S (u ++ [τ u]) :=
      ⟨fun u => Classical.choose (hpoint u), fun u hu => Classical.choose_spec (hpoint u) hu⟩
    refine ⟨τ, fun σ => ?_⟩
    have key : ∀ n, ¬ IWinQ S (hist σ τ [] n) := by
      intro n
      induction n with
      | zero => exact hI
      | succ n ih =>
          rw [hist_succ]
          by_cases hpar : (hist σ τ [] n).length % 2 = 0
          · intro hcon
            refine ih (iwinq_of_move_I hpar (a := σ (hist σ τ [] n)) ?_)
            rwa [show nextMove σ τ (hist σ τ [] n) = σ (hist σ τ [] n) from
              if_pos hpar] at hcon
          · have hex : ∃ a : A, ¬ IWinQ S (hist σ τ [] n ++ [a]) :=
              Classical.byContradiction fun hall =>
                ih (iwinq_of_move_II hpar fun a =>
                  Classical.byContradiction fun hna => hall ⟨a, hna⟩)
            rw [show nextMove σ τ (hist σ τ [] n) = τ (hist σ τ [] n) from if_neg hpar]
            exact hτ _ hex
    intro hcon
    obtain ⟨n, hn⟩ := hW1 _ hcon
    rw [← hist_nil_eq_pre] at hn
    exact key n ⟨fun _ => Classical.choice inferInstance, WinBy.base hn⟩

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

