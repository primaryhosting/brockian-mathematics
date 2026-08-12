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

namespace Frontier

section GaleStewart

variable {A : Type*}

/-- In a two–player game on the move set `A`, the players alternate moves, player I moving at
positions of even length and player II at positions of odd length.  Given strategies `σ` for
player I and `τ` for player II, `nextMove σ τ p` is the move played at the position `p`. -/
def nextMove (σ τ : List A → A) (p : List A) : A :=
  if Even p.length then σ p else τ p

/-- `run σ τ p n` is the position reached after `n` further moves, starting from the position `p`,
when the players follow the strategies `σ` and `τ`. -/
def run (σ τ : List A → A) (p : List A) : ℕ → List A
  | 0 => p
  | n + 1 => run σ τ p n ++ [nextMove σ τ (run σ τ p n)]

/-- `play a₀ σ τ p` is the infinite play obtained by starting from the position `p` and letting
the players follow the strategies `σ` and `τ`.  Its first `p.length` moves are those of `p`. -/
def play (a₀ : A) (σ τ : List A → A) (p : List A) (i : ℕ) : A :=
  if i < p.length then p.getD i a₀ else nextMove σ τ (run σ τ p (i - p.length))

/-- Player I wins the game with payoff set `W` from the position `p` if he has a strategy from `p`
beating every strategy of player II. -/
def WinsFrom (a₀ : A) (W : Set (ℕ → A)) (p : List A) : Prop :=
  ∃ σ : List A → A, ∀ τ : List A → A, play a₀ σ τ p ∈ W

lemma run_length (σ τ : List A → A) (p : List A) (n : ℕ) :
    (run σ τ p n).length = p.length + n := by
  induction n with
  | zero => simp [run]
  | succ n ih => simp [run, ih]; omega

lemma run_eq_append (σ τ : List A → A) (p : List A) (n : ℕ) :
    ∃ t : List A, run σ τ p n = p ++ t := by
  induction n with
  | zero => exact ⟨[], by simp [run]⟩
  | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨t ++ [nextMove σ τ (run σ τ p n)], by simp [run, ht]⟩

lemma run_getD_of_lt (a₀ : A) (σ τ : List A → A) (p : List A) (n i : ℕ) (hi : i < p.length) :
    (run σ τ p n).getD i a₀ = p.getD i a₀ := by
  obtain ⟨t, ht⟩ := run_eq_append σ τ p n
  rw [ht, List.getD_append _ _ _ _ hi]

lemma play_of_lt (a₀ : A) (σ τ : List A → A) (p : List A) (i : ℕ) (hi : i < p.length) :
    play a₀ σ τ p i = p.getD i a₀ := by
  simp [play, hi]

lemma play_length_add (a₀ : A) (σ τ : List A → A) (p : List A) (k : ℕ) :
    play a₀ σ τ p (p.length + k) = nextMove σ τ (run σ τ p k) := by
  simp [play]

/-- The `n`-th position of a run determines the first `p.length + n` moves of the play. -/
lemma run_getD_eq_play (a₀ : A) (σ τ : List A → A) (p : List A) (n i : ℕ)
    (hi : i < p.length + n) : (run σ τ p n).getD i a₀ = play a₀ σ τ p i := by
  induction n with
  | zero =>
      have : i < p.length := by simpa using hi
      simp [run, play, this]
  | succ n ih =>
      rcases lt_or_ge i (p.length + n) with h | h
      · have hlen : i < (run σ τ p n).length := by rw [run_length]; exact h
        rw [show run σ τ p (n + 1)
              = run σ τ p n ++ [nextMove σ τ (run σ τ p n)] from rfl,
          List.getD_append _ _ _ _ hlen]
        exact ih h
      · have hi' : i = p.length + n := by omega
        subst hi'
        rw [show run σ τ p (n + 1)
              = run σ τ p n ++ [nextMove σ τ (run σ τ p n)] from rfl]
        rw [List.getD_append_right _ _ _ _ (by rw [run_length]), run_length]
        simp [play_length_add]

/-- Two plays that agree on the first `n` moves. -/
lemma play_ext_of_run_eq {a₀ : A} {σ τ σ' τ' : List A → A} {p q : List A} {m k : ℕ}
    (h : ∀ n : ℕ, run σ τ p (n + m) = run σ' τ' q (n + k)) :
    play a₀ σ τ p = play a₀ σ' τ' q := by
  funext i
  have h1 : i < p.length + (i + 1 + m) := by omega
  have h2 : i < q.length + (i + 1 + k) := by omega
  rw [← run_getD_eq_play a₀ σ τ p (i + 1 + m) i h1,
    ← run_getD_eq_play a₀ σ' τ' q (i + 1 + k) i h2, h (i + 1)]

/-- If player I can win from `p ++ [a]`, then he can win from `p`, provided it is his turn at `p`
(so that he can play `a`). -/
lemma winsFrom_of_winsFrom_append (a₀ : A) (W : Set (ℕ → A)) (p : List A)
    (hp : Even p.length) (a : A) (h : WinsFrom a₀ W (p ++ [a])) : WinsFrom a₀ W p := by
  obtain ⟨σ, hσ⟩ := h
  classical
  refine ⟨fun q => if q = p then a else σ q, fun τ => ?_⟩
  set σ' : List A → A := fun q => if q = p then a else σ q with hσ'
  have key : ∀ n : ℕ, run σ' τ p (n + 1) = run σ τ (p ++ [a]) (n + 0) := by
    intro n
    induction n with
    | zero =>
        show run σ' τ p 0 ++ [nextMove σ' τ (run σ' τ p 0)] = _
        simp [run, nextMove, hp, hσ']
    | succ n ih =>
        show run σ' τ p (n + 1) ++ [nextMove σ' τ (run σ' τ p (n + 1))] = _
        simp only [Nat.add_zero] at ih ⊢
        rw [ih]
        have hlen : p.length < (run σ τ (p ++ [a]) n).length := by
          rw [run_length]; simp; omega
        have hne : run σ τ (p ++ [a]) n ≠ p := by
          intro hcon
          rw [hcon] at hlen
          exact lt_irrefl _ hlen
        show _ = run σ τ (p ++ [a]) n ++ [nextMove σ τ (run σ τ (p ++ [a]) n)]
        simp [nextMove, hσ', hne]
  have := play_ext_of_run_eq (a₀ := a₀) (σ := σ') (τ := τ) (σ' := σ) (τ' := τ)
    (p := p) (q := p ++ [a]) (m := 1) (k := 0) key
  rw [this]
  exact hσ τ

/-- If it is player II's turn at `p` and player I can win from `p ++ [a]` for every move `a`,
then player I can win from `p`. -/
lemma winsFrom_of_forall_winsFrom_append (a₀ : A) (W : Set (ℕ → A)) (p : List A)
    (hp : ¬ Even p.length) (h : ∀ a : A, WinsFrom a₀ W (p ++ [a])) : WinsFrom a₀ W p := by
  classical
  choose f hf using h
  refine ⟨fun q => f (q.getD p.length a₀) q, fun τ => ?_⟩
  set σ : List A → A := fun q => f (q.getD p.length a₀) q with hσdef
  set b : A := τ p with hb
  have hpb : (p ++ [b]).length = p.length + 1 := by simp
  have hgetb : ∀ n : ℕ, (run (f b) τ (p ++ [b]) n).getD p.length a₀ = b := by
    intro n
    rw [run_getD_of_lt a₀ (f b) τ (p ++ [b]) n p.length (by rw [hpb]; omega)]
    simp
  have key : ∀ n : ℕ, run σ τ p (n + 1) = run (f b) τ (p ++ [b]) (n + 0) := by
    intro n
    induction n with
    | zero =>
        show run σ τ p 0 ++ [nextMove σ τ (run σ τ p 0)] = _
        simp [run, nextMove, hp, hb]
    | succ n ih =>
        show run σ τ p (n + 1) ++ [nextMove σ τ (run σ τ p (n + 1))] = _
        simp only [Nat.add_zero] at ih ⊢
        rw [ih]
        show _ = run (f b) τ (p ++ [b]) n ++ [nextMove (f b) τ (run (f b) τ (p ++ [b]) n)]
        simp only [nextMove, hσdef, hgetb n]
  have := play_ext_of_run_eq (a₀ := a₀) (σ := σ) (τ := τ) (σ' := f b) (τ' := τ)
    (p := p) (q := p ++ [b]) (m := 1) (k := 0) key
  rw [this]
  exact hf b τ

/-- A defensive strategy for player II: at a position from which player I has no winning
strategy, play a move preserving that fact. -/
noncomputable def defensive (a₀ : A) (W : Set (ℕ → A)) (p : List A) : A := by
  classical
  exact if h : ∃ a : A, ¬ WinsFrom a₀ W (p ++ [a]) then h.choose else a₀

lemma defensive_spec (a₀ : A) (W : Set (ℕ → A)) (p : List A)
    (h : ∃ a : A, ¬ WinsFrom a₀ W (p ++ [a])) :
    ¬ WinsFrom a₀ W (p ++ [defensive a₀ W p]) := by
  classical
  have : defensive a₀ W p = h.choose := by
    simp only [defensive]
    rw [dif_pos h]
  rw [this]
  exact h.choose_spec

/-- Every point of an open subset of the Baire-type space `ℕ → A` (with `A` discrete) has a
basic cylinder neighbourhood contained in the set. -/
lemma exists_prefix_subset [TopologicalSpace A] [DiscreteTopology A] {W : Set (ℕ → A)}
    (hW : IsOpen W) {x : ℕ → A} (hx : x ∈ W) :
    ∃ n : ℕ, ∀ y : ℕ → A, (∀ i < n, y i = x i) → y ∈ W := by
  obtain ⟨v, ⟨x', n, rfl⟩, hxv, hvW⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => A)).exists_subset_of_mem_open hx hW
  refine ⟨n, fun y hy => ?_⟩
  apply hvW
  have hxx' : PiNat.cylinder x n = PiNat.cylinder x' n := PiNat.mem_cylinder_iff_eq.1 hxv
  rw [← hxx']
  exact PiNat.mem_cylinder_iff.2 hy

/-- **Gale–Stewart theorem**: every open game is determined.  Here a game is given by a move set
`A` (discrete, nonempty) and a payoff set `W ⊆ (ℕ → A)` for player I; the players alternately
choose elements of `A`, player I starting, and player I wins the resulting play `x : ℕ → A`
iff `x ∈ W`.  If `W` is open, then either player I has a winning strategy, or player II has one. -/
theorem Gale_Stewart_open [TopologicalSpace A] [DiscreteTopology A] (a₀ : A)
    (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : List A → A, ∀ τ : List A → A, play a₀ σ τ [] ∈ W) ∨
      (∃ τ : List A → A, ∀ σ : List A → A, play a₀ σ τ [] ∉ W) := by
  classical
  by_cases hI : WinsFrom a₀ W []
  · exact Or.inl hI
  refine Or.inr ⟨defensive a₀ W, fun σ hmem => ?_⟩
  set τ : List A → A := defensive a₀ W with hτ
  -- along the play, player I never has a winning strategy
  have hrun : ∀ n : ℕ, ¬ WinsFrom a₀ W (run σ τ [] n) := by
    intro n
    induction n with
    | zero => simpa [run] using hI
    | succ n ih =>
        show ¬ WinsFrom a₀ W (run σ τ [] n ++ [nextMove σ τ (run σ τ [] n)])
        set q : List A := run σ τ [] n with hq
        by_cases hpar : Even q.length
        · intro hwin
          exact ih (winsFrom_of_winsFrom_append a₀ W q hpar _
            (by simpa [nextMove, hpar] using hwin))
        · have hex : ∃ a : A, ¬ WinsFrom a₀ W (q ++ [a]) := by
            by_contra hcon
            push_neg at hcon
            exact ih (winsFrom_of_forall_winsFrom_append a₀ W q hpar hcon)
          have := defensive_spec a₀ W q hex
          simpa [nextMove, hpar, hτ] using this
  -- but the play is in the open set `W`, so some finite position already secures a win
  obtain ⟨n, hn⟩ := exists_prefix_subset hW hmem
  refine hrun n ⟨fun _ => a₀, fun τ' => ?_⟩
  apply hn
  intro i hi
  have hlen : (run σ τ [] n).length = n := by rw [run_length]; simp
  have hi' : i < (run σ τ [] n).length := by omega
  rw [play_of_lt a₀ _ τ' _ i hi']
  rw [run_getD_eq_play a₀ σ τ [] n i (by simpa using hi)]

end GaleStewart

end Frontier

