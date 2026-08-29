/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the infinite play `x`. -/
def prefixOf (x : ℕ → A) (n : ℕ) : List A := List.ofFn (fun i : Fin n => x i)

@[simp] lemma length_prefixOf (x : ℕ → A) (n : ℕ) : (prefixOf x n).length = n := by
  simp [prefixOf]

lemma prefixOf_succ (x : ℕ → A) (n : ℕ) :
    prefixOf x (n + 1) = prefixOf x n ++ [x n] := by
  rw [prefixOf, prefixOf, List.ofFn_succ']
  simp [List.concat_eq_append]

lemma prefixOf_eq_iff (x y : ℕ → A) (n : ℕ) :
    prefixOf x n = prefixOf y n ↔ ∀ i < n, x i = y i := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simpa [prefixOf, List.getElem?_ofFn, hi] using this
  · intro h
    simp only [prefixOf, List.ofFn_inj]
    funext i
    exact h i i.isLt

lemma getElem_prefixOf (x : ℕ → A) (n i : ℕ) (hi : i < (prefixOf x n).length) :
    (prefixOf x n)[i] = x i := by
  simp [prefixOf]

/-- The position (list of moves played so far) after `n` moves, when both players
follow the combined strategy `s`. -/
def playPos (s : List A → A) : ℕ → List A
  | 0 => []
  | n + 1 => playPos s n ++ [s (playPos s n)]

/-- The infinite play resulting from the combined strategy `s`. -/
def play (s : List A → A) : ℕ → A := fun n => s (playPos s n)

lemma playPos_eq_prefixOf (s : List A → A) (n : ℕ) :
    playPos s n = prefixOf (play s) n := by
  induction n with
  | zero => simp [playPos, prefixOf]
  | succ n ih => rw [playPos, ih, prefixOf_succ, play]; rw [ih]

lemma play_eq (s : List A → A) (n : ℕ) : play s n = s (prefixOf (play s) n) := by
  rw [play, playPos_eq_prefixOf]

/-- Combine a strategy `σ` for player I (who moves at positions of even length) with a
strategy `τ` for player II (who moves at positions of odd length). -/
def combine (σ τ : List A → A) : List A → A :=
  fun p => if Even p.length then σ p else τ p

/-- `Iwin W p` : player I can force, from the position `p`, that the play ends up in the
open set `W`; the "base" case records that the position `p` already secures `W`. -/
inductive Iwin (W : Set (ℕ → A)) : List A → Prop
  | base (p : List A) : (∀ x : ℕ → A, prefixOf x p.length = p → x ∈ W) → Iwin W p
  | stepI (p : List A) (a : A) : Even p.length → Iwin W (p ++ [a]) → Iwin W p
  | stepII (p : List A) : ¬ Even p.length → (∀ a : A, Iwin W (p ++ [a])) → Iwin W p

section

variable [Nonempty A] (W : Set (ℕ → A))

/-- If `Iwin W p`, then player I has a strategy which, from position `p`, forces `W`. -/
lemma exists_strategy_of_Iwin (p : List A) (h : Iwin W p) :
    ∃ σ : List A → A, ∀ s : List A → A,
      (∀ n, Even n → p.length ≤ n → s (prefixOf (play s) n) = σ (prefixOf (play s) n)) →
      prefixOf (play s) p.length = p → play s ∈ W := by
  classical
  induction h with
  | base p hb =>
      exact ⟨fun _ => Classical.arbitrary A, fun s _ hpref => hb _ hpref⟩
  | stepI p a hev _ ih =>
      obtain ⟨σ', hσ'⟩ := ih
      refine ⟨fun q => if q = p then a else σ' q, ?_⟩
      intro s hagree hpref
      have hxp : play s p.length = a := by
        rw [play_eq, hpref]
        have h2 := hagree p.length hev le_rfl
        rw [hpref] at h2
        simpa using h2
      have hpref' : prefixOf (play s) (p ++ [a]).length = p ++ [a] := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [show p.length + (0 + 1) = p.length + 1 by ring, prefixOf_succ, hpref, hxp]
      refine hσ' s ?_ hpref'
      intro n hn hle
      simp only [List.length_append, List.length_cons, List.length_nil] at hle
      have hlt : p.length < n := by omega
      have hne : prefixOf (play s) n ≠ p := by
        intro hc
        have h3 := congrArg List.length hc
        simp at h3
        omega
      have h4 := hagree n hn (le_of_lt hlt)
      simpa [hne] using h4
  | stepII p hodd _ ih =>
      choose f hf using ih
      refine ⟨fun q => if hq : p.length < q.length then f (q[p.length]) q
        else Classical.arbitrary A, ?_⟩
      intro s hagree hpref
      set a := play s p.length with ha
      have hpref' : prefixOf (play s) (p ++ [a]).length = p ++ [a] := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [show p.length + (0 + 1) = p.length + 1 by ring, prefixOf_succ, hpref]
      refine hf a s ?_ hpref'
      intro n hn hle
      simp only [List.length_append, List.length_cons, List.length_nil] at hle
      have hlt : p.length < n := by omega
      have hlt' : p.length < (prefixOf (play s) n).length := by simpa using hlt
      have h5 := hagree n hn (le_of_lt hlt)
      rw [h5]
      simp only [dif_pos hlt', getElem_prefixOf, ha]

/-- If player I cannot force `W` from the empty position, player II has a strategy which
avoids all positions from which player I can force `W`. -/
lemma exists_strategy_of_not_Iwin (h : ¬ Iwin W []) :
    ∃ τ : List A → A, ∀ σ : List A → A, ∀ n : ℕ,
      ¬ Iwin W (prefixOf (play (combine σ τ)) n) := by
  classical
  refine ⟨fun p => if hp : ∃ a, ¬ Iwin W (p ++ [a]) then Classical.choose hp
    else Classical.arbitrary A, ?_⟩
  set τ : List A → A := fun p => if hp : ∃ a, ¬ Iwin W (p ++ [a]) then Classical.choose hp
    else Classical.arbitrary A with hτdef
  intro σ n
  induction n with
  | zero => simpa [prefixOf] using h
  | succ n ih =>
      rw [prefixOf_succ]
      intro hcon
      set x := play (combine σ τ) with hx
      set p := prefixOf x n with hp
      have hlen : p.length = n := by simp [hp]
      by_cases he : Even n
      · exact ih (Iwin.stepI p (x n) (by rw [hlen]; exact he) hcon)
      · have hxn : x n = τ p := by
          rw [hx, play_eq]
          simp only [combine, ← hp, ← hx]
          rw [if_neg (by rw [hlen]; exact he)]
        have hex : ∃ a, ¬ Iwin W (p ++ [a]) := by
          by_contra hall
          push_neg at hall
          exact ih (Iwin.stepII p (by rw [hlen]; exact he) hall)
        have hchoice : τ p = Classical.choose hex := by
          rw [hτdef]; simp only [dif_pos hex]
        rw [hxn, hchoice] at hcon
        exact Classical.choose_spec hex hcon

end

/-- Openness of `W` in the product topology of the discrete space `A`: every play in `W`
has a finite prefix all of whose extensions lie in `W`. -/
lemma exists_prefix_subset_of_isOpen {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    {W : Set (ℕ → A)} (hW : IsOpen W) {x : ℕ → A} (hx : x ∈ W) :
    ∃ n : ℕ, ∀ y : ℕ → A, (∀ i < n, y i = x i) → y ∈ W := by
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hW x hx
  refine ⟨(I.sup id) + 1, fun y hy => ?_⟩
  refine hsub (fun i hi => ?_)
  rw [hy i (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))]
  exact (hu i hi).2

/-- **Gale–Stewart**: every open game is determined. Here a strategy is a map from
positions (finite lists of previous moves) to moves; player I moves at positions of even
length, player II at positions of odd length; player I wins a play iff it belongs to the
payoff set `W`, which is assumed open in the product topology on `ℕ → A` (with `A`
discrete). Then either player I has a winning strategy, or player II has one. -/
theorem Gale_Stewart_open {A : Type*} [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : List A → A, ∀ τ : List A → A, play (combine σ τ) ∈ W) ∨
    (∃ τ : List A → A, ∀ σ : List A → A, play (combine σ τ) ∉ W) := by
  by_cases h : Iwin W ([] : List A)
  · left
    obtain ⟨σ, hσ⟩ := exists_strategy_of_Iwin W [] h
    refine ⟨σ, fun τ => hσ (combine σ τ) ?_ ?_⟩
    · intro n hn _
      have hlen : Even (prefixOf (play (combine σ τ)) n).length := by simpa using hn
      simp only [combine, if_pos hlen]
    · simp [prefixOf]
  · right
    obtain ⟨τ, hτ⟩ := exists_strategy_of_not_Iwin W h
    refine ⟨τ, fun σ hmem => ?_⟩
    obtain ⟨n, hn⟩ := exists_prefix_subset_of_isOpen hW hmem
    refine hτ σ n (Iwin.base _ ?_)
    intro y hy
    exact hn y ((prefixOf_eq_iff y (play (combine σ τ)) n).mp (by simpa using hy))

end Frontier

