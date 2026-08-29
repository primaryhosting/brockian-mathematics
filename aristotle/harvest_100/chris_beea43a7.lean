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

/-!
## Setting

We formalize infinite two-player games with perfect information on a set `A` of moves.

A *play* is an element of `ℕ → A`. Player I chooses the moves with even index, Player II the
moves with odd index. A *strategy* for either player is a function `List A → A` assigning a
move to each position (a finite list of moves played so far, in order). The payoff set
`W : Set (ℕ → A)` is the set of plays won by Player I.

`gsPos σ τ p n` is the position reached after `n` further moves when the play starts from
position `p` and the players follow `σ` (Player I) and `τ` (Player II); `gsRun σ τ p` is the
resulting infinite play.

The main theorem `Frontier.Gale_Stewart_open` states the Gale–Stewart theorem: if the payoff
set `W` is open (for the product topology on `ℕ → A` with `A` discrete) then the game is
determined, i.e. one of the two players has a winning strategy.
-/

namespace Frontier

variable {A : Type*}

/-- The position reached after `n` moves starting from position `p`, when Player I follows the
strategy `σ` and Player II follows the strategy `τ`.  The player to move at a position `q` is
Player I if `q.length` is even and Player II otherwise. -/
def gsPos (σ τ : List A → A) (p : List A) : ℕ → List A
  | 0 => p
  | n + 1 => let q := gsPos σ τ p n; q ++ [if Even q.length then σ q else τ q]

@[simp] lemma gsPos_zero (σ τ : List A → A) (p : List A) : gsPos σ τ p 0 = p := rfl

lemma gsPos_succ (σ τ : List A → A) (p : List A) (n : ℕ) :
    gsPos σ τ p (n + 1) =
      gsPos σ τ p n ++ [if Even (gsPos σ τ p n).length then σ (gsPos σ τ p n)
        else τ (gsPos σ τ p n)] := rfl

/-- The infinite play resulting from the strategies `σ`, `τ` starting at the position `p`. -/
noncomputable def gsRun [Nonempty A] (σ τ : List A → A) (p : List A) (n : ℕ) : A :=
  (gsPos σ τ p (n + 1)).getD n (Classical.arbitrary A)

/-- Player I has a winning strategy in the game with payoff set `W` starting from position `p`. -/
def IWins [Nonempty A] (W : Set (ℕ → A)) (p : List A) : Prop :=
  ∃ σ : List A → A, ∀ τ : List A → A, gsRun σ τ p ∈ W

/-! ### Basic properties of positions and runs -/

lemma gsPos_length (σ τ : List A → A) (p : List A) (n : ℕ) :
    (gsPos σ τ p n).length = p.length + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [gsPos_succ]; simp [ih]; omega

lemma gsPos_prefix_succ (σ τ : List A → A) (p : List A) (n : ℕ) :
    gsPos σ τ p n <+: gsPos σ τ p (n + 1) := by
  rw [gsPos_succ]; exact ⟨_, rfl⟩

lemma gsPos_prefix (σ τ : List A → A) (p : List A) {n m : ℕ} (h : n ≤ m) :
    gsPos σ τ p n <+: gsPos σ τ p m := by
  induction m with
  | zero => simp_all
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (gsPos_prefix_succ σ τ p m)
    · subst h'; exact List.prefix_rfl

lemma prefix_getD {l₁ l₂ : List A} (h : l₁ <+: l₂) {n : ℕ} (hn : n < l₁.length) (d : A) :
    l₂.getD n d = l₁.getD n d := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hn]

lemma gsPos_prefix_self (σ τ : List A → A) (p : List A) (n : ℕ) : p <+: gsPos σ τ p n := by
  simpa using gsPos_prefix σ τ p (Nat.zero_le n)

/-- Any sufficiently long position of the run reads off the values of the run. -/
lemma gsPos_getD_eq_run [Nonempty A] (σ τ : List A → A) (p : List A) {m n : ℕ}
    (hn : n < (gsPos σ τ p m).length) :
    (gsPos σ τ p m).getD n (Classical.arbitrary A) = gsRun σ τ p n := by
  set d := Classical.arbitrary A
  have hn' : n < (gsPos σ τ p (n + 1)).length := by rw [gsPos_length]; omega
  have h1 : (gsPos σ τ p (max m (n + 1))).getD n d = (gsPos σ τ p m).getD n d :=
    prefix_getD (gsPos_prefix σ τ p (le_max_left m (n + 1))) hn d
  have h2 : (gsPos σ τ p (max m (n + 1))).getD n d = (gsPos σ τ p (n + 1)).getD n d :=
    prefix_getD (gsPos_prefix σ τ p (le_max_right m (n + 1))) hn' d
  rw [← h1, h2]; rfl

lemma gsRun_eq_of_lt [Nonempty A] (σ τ : List A → A) (p : List A) {n : ℕ} (hn : n < p.length) :
    gsRun σ τ p n = p.getD n (Classical.arbitrary A) := by
  have := gsPos_getD_eq_run σ τ p (m := 0) (n := n) (by simpa using hn)
  simpa using this.symm

/-- The run only depends on the values of the strategies at positions extending `p`. -/
lemma gsPos_congr {σ τ σ' τ' : List A → A} {p : List A}
    (hσ : ∀ q, p <+: q → σ q = σ' q) (hτ : ∀ q, p <+: q → τ q = τ' q) (n : ℕ) :
    gsPos σ τ p n = gsPos σ' τ' p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : p <+: gsPos σ τ p n := gsPos_prefix_self σ τ p n
    rw [gsPos_succ, gsPos_succ, ← ih, hσ _ hpre, hτ _ hpre]

lemma gsRun_congr [Nonempty A] {σ τ σ' τ' : List A → A} {p : List A}
    (hσ : ∀ q, p <+: q → σ q = σ' q) (hτ : ∀ q, p <+: q → τ q = τ' q) :
    gsRun σ τ p = gsRun σ' τ' p := by
  funext n; unfold gsRun; rw [gsPos_congr hσ hτ]

/-- Playing one move from `p` shifts the position sequence. -/
lemma gsPos_shift {σ τ : List A → A} {p : List A} {a : A}
    (h : (if Even p.length then σ p else τ p) = a) (n : ℕ) :
    gsPos σ τ p (n + 1) = gsPos σ τ (p ++ [a]) n := by
  induction n with
  | zero => rw [gsPos_succ]; simp [h]
  | succ n ih => rw [gsPos_succ, ih, gsPos_succ]

lemma gsRun_shift [Nonempty A] {σ τ : List A → A} {p : List A} {a : A}
    (h : (if Even p.length then σ p else τ p) = a) :
    gsRun σ τ p = gsRun σ τ (p ++ [a]) := by
  funext n
  have h1 : n < (gsPos σ τ p (n + 2)).length := by rw [gsPos_length]; omega
  have h2 : (gsPos σ τ p (n + 2)).getD n (Classical.arbitrary A) = gsRun σ τ p n :=
    gsPos_getD_eq_run σ τ p h1
  rw [← h2, gsPos_shift h (n + 1)]
  exact gsPos_getD_eq_run σ τ (p ++ [a]) (by rw [gsPos_length]; simp; omega)

/-! ### The key combinatorial steps -/

/-- If Player I is to move at `p` and some move leads to a position won by Player I, then
Player I wins from `p`. -/
lemma iwins_of_move_even [Nonempty A] {W : Set (ℕ → A)} {p : List A} (hp : Even p.length)
    {a : A} (h : IWins W (p ++ [a])) : IWins W p := by
  classical
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun q => if q = p then a else σ q, fun τ => ?_⟩
  set σ' : List A → A := fun q => if q = p then a else σ q with hσ'
  have hstep : (if Even p.length then σ' p else τ p) = a := by simp [hp, hσ']
  have h1 : gsRun σ' τ p = gsRun σ' τ (p ++ [a]) := gsRun_shift hstep
  have h2 : gsRun σ' τ (p ++ [a]) = gsRun σ τ (p ++ [a]) := by
    refine gsRun_congr (fun q hq => ?_) (fun q _ => rfl)
    have hlen : (p ++ [a]).length ≤ q.length := hq.length_le
    have : q ≠ p := by
      intro hqp; subst hqp; simp at hlen
    simp [hσ', this]
  rw [h1, h2]
  exact hσ τ

/-- If Player II is to move at `p` and every move leads to a position won by Player I, then
Player I wins from `p`. -/
lemma iwins_of_moves_odd [Nonempty A] {W : Set (ℕ → A)} {p : List A} (hp : ¬ Even p.length)
    (h : ∀ a : A, IWins W (p ++ [a])) : IWins W p := by
  classical
  choose f hf using h
  set d := Classical.arbitrary A with hd
  refine ⟨fun q => if p.length < q.length then f (q.getD p.length d) q else d, fun τ => ?_⟩
  set σ' : List A → A :=
    fun q => if p.length < q.length then f (q.getD p.length d) q else d with hσ'
  set a := τ p with ha
  have hstep : (if Even p.length then σ' p else τ p) = a := by simp [hp, ha]
  have h1 : gsRun σ' τ p = gsRun σ' τ (p ++ [a]) := gsRun_shift hstep
  have h2 : gsRun σ' τ (p ++ [a]) = gsRun (f a) τ (p ++ [a]) := by
    refine gsRun_congr (fun q hq => ?_) (fun q _ => rfl)
    have hlen : (p ++ [a]).length ≤ q.length := hq.length_le
    have hlt : p.length < q.length := by simp at hlen; omega
    have hval : q.getD p.length d = a := by
      rw [prefix_getD hq (by simp) d]; simp
    show (if p.length < q.length then f (q.getD p.length d) q else d) = f a q
    rw [if_pos hlt, hval]
  rw [h1, h2]
  exact hf a τ

/-- If Player I never wins from any position of a run, then the run is not in the open set `W`. -/
lemma run_not_mem_of_forall_not_iwins [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    {W : Set (ℕ → A)} (hW : IsOpen W) {σ τ : List A → A}
    (h : ∀ n, ¬ IWins W (gsPos σ τ [] n)) : gsRun σ τ [] ∉ W := by
  intro hmem
  set x := gsRun σ τ [] with hx
  -- openness gives a finite prefix of `x` all of whose extensions lie in `W`
  obtain ⟨n, hn⟩ : ∃ n, ∀ y : ℕ → A, (∀ i < n, y i = x i) → y ∈ W := by
    rw [isOpen_pi_iff] at hW
    obtain ⟨I, u, hu, hsub⟩ := hW x hmem
    refine ⟨(I.sup id) + 1, fun y hy => hsub ?_⟩
    intro i hi
    have h1 : i ≤ I.sup id := by simpa using Finset.le_sup (f := id) hi
    have : y i = x i := hy i (by omega)
    rw [this]
    exact (hu i hi).2
  set q := gsPos σ τ [] n with hq
  have hqlen : q.length = n := by rw [hq, gsPos_length]; simp
  refine h n ⟨fun _ => Classical.arbitrary A, fun τ' => ?_⟩
  refine hn _ (fun i hi => ?_)
  have h1 : gsRun (fun _ => Classical.arbitrary A) τ' q i = q.getD i (Classical.arbitrary A) :=
    gsRun_eq_of_lt _ _ _ (by omega)
  have h2 : q.getD i (Classical.arbitrary A) = x i :=
    gsPos_getD_eq_run σ τ [] (by rw [gsPos_length]; simpa using hi)
  rw [h1, h2]

/-! ### The Gale–Stewart theorem -/

/-- **Gale–Stewart theorem**: every open game is determined.

The moves are taken from a nonempty set `A` carrying the discrete topology, and the set `W` of
plays winning for Player I is open in the product topology on `ℕ → A`.  Positions are finite
lists of moves; Player I moves at positions of even length and Player II at positions of odd
length; `gsRun σ τ []` is the play resulting from the strategies `σ` (Player I) and `τ`
(Player II).  The conclusion is that either Player I has a strategy forcing the play into `W`,
or Player II has a strategy forcing the play outside `W`. -/
theorem Gale_Stewart_open {A : Type*} [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : List A → A, ∀ τ : List A → A, gsRun σ τ [] ∈ W) ∨
    (∃ τ : List A → A, ∀ σ : List A → A, gsRun σ τ [] ∉ W) := by
  classical
  by_cases hI : IWins W ([] : List A)
  · exact Or.inl hI
  refine Or.inr ⟨fun p => if h : ∃ a : A, ¬ IWins W (p ++ [a]) then h.choose
    else Classical.arbitrary A, fun σ => ?_⟩
  set τ : List A → A := fun p => if h : ∃ a : A, ¬ IWins W (p ++ [a]) then h.choose
    else Classical.arbitrary A with hτ
  refine run_not_mem_of_forall_not_iwins hW (fun n => ?_)
  induction n with
  | zero => simpa using hI
  | succ n ih =>
    rw [gsPos_succ]
    set q := gsPos σ τ [] n with hq
    by_cases hpar : Even q.length
    · simp only [hpar, if_true]
      exact fun hw => ih (iwins_of_move_even hpar hw)
    · simp only [hpar, if_false]
      have hex : ∃ a : A, ¬ IWins W (q ++ [a]) := by
        by_contra hcon
        push_neg at hcon
        exact ih (iwins_of_moves_odd hpar hcon)
      have : τ q = hex.choose := by rw [hτ]; simp [hex]
      rw [this]
      exact hex.choose_spec

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

