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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
# The Gale–Stewart theorem: open games are determined

We consider the infinite two-player game on a nonempty set of moves `A`.  A play is a
sequence `x : ℕ → A`; player I chooses the moves at even indices, player II the moves at
odd indices.  Player I wins the play `x` if `x ∈ W`, otherwise player II wins.

A *strategy* is a function `List A → A`, taking the history of the play so far (as a list,
in chronological order) to the next move.  Given a starting position `p : List A` and
strategies `σ` (for I) and `τ` (for II), the resulting play is `play p σ τ`.

The Gale–Stewart theorem states that if `W` is open (in the product topology, `A` being
discrete), then the game is determined: one of the two players has a winning strategy.
-/

variable {A : Type*}

/-- The history of the play after `n` further moves, starting from the position `p`,
when player I follows `σ` and player II follows `τ`.  The player to move at a position
`l` is player I if `l.length` is even and player II if `l.length` is odd. -/
def hist (p : List A) (σ τ : List A → A) : ℕ → List A
  | 0 => p
  | n + 1 =>
      (hist p σ τ n) ++
        [if Even (hist p σ τ n).length then σ (hist p σ τ n) else τ (hist p σ τ n)]

/-- The infinite play resulting from the position `p` and the strategies `σ` (player I)
and `τ` (player II). -/
noncomputable def play [Nonempty A] (p : List A) (σ τ : List A → A) (i : ℕ) : A :=
  (hist p σ τ (i + 1)).getD i (Classical.arbitrary A)

/-- Player I wins the game with payoff set `W` from the position `p` if he has a strategy
which defeats every strategy of player II. -/
def WinI [Nonempty A] (W : Set (ℕ → A)) (p : List A) : Prop :=
  ∃ σ : List A → A, ∀ τ : List A → A, play p σ τ ∈ W

section Basic

variable (p : List A) (σ τ : List A → A)

@[simp] lemma hist_zero : hist p σ τ 0 = p := rfl

lemma hist_succ (n : ℕ) :
    hist p σ τ (n + 1) =
      (hist p σ τ n) ++
        [if Even (hist p σ τ n).length then σ (hist p σ τ n) else τ (hist p σ τ n)] := rfl

lemma hist_length (n : ℕ) : (hist p σ τ n).length = p.length + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [hist_succ]; simp [ih]; omega

lemma hist_prefix_succ (n : ℕ) : hist p σ τ n <+: hist p σ τ (n + 1) := by
  rw [hist_succ]; exact List.prefix_append _ _

lemma hist_prefix_mono {m n : ℕ} (h : m ≤ n) : hist p σ τ m <+: hist p σ τ n := by
  induction n with
  | zero => simp_all
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h1 | h1
    · exact (ih (by omega)).trans (hist_prefix_succ p σ τ n)
    · have : m = n + 1 := by omega
      simp [this]

lemma prefix_hist (n : ℕ) : p <+: hist p σ τ n := by
  have := hist_prefix_mono p σ τ (Nat.zero_le n)
  simpa using this

lemma getD_of_prefix {l₁ l₂ : List A} (h : l₁ <+: l₂) (i : ℕ) (hi : i < l₁.length) (d : A) :
    l₂.getD i d = l₁.getD i d := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

variable [Nonempty A]

/-- The value of the play at index `i` can be read off from any long enough history. -/
lemma play_eq_getD (i m : ℕ) (h : i < p.length + m) :
    play p σ τ i = (hist p σ τ m).getD i (Classical.arbitrary A) := by
  rcases le_total (i + 1) m with hm | hm
  · rw [play, getD_of_prefix (hist_prefix_mono p σ τ hm) i (by rw [hist_length]; omega)]
  · rw [play, getD_of_prefix (hist_prefix_mono p σ τ hm) i (by rw [hist_length]; omega)]

/-- The play starting from `p` extends `p`. -/
lemma play_eq_of_lt_length (i : ℕ) (h : i < p.length) :
    play p σ τ i = p.getD i (Classical.arbitrary A) := by
  rw [play_eq_getD p σ τ i 0 (by omega)]
  rfl

end Basic

section Steps

variable [Nonempty A] {W : Set (ℕ → A)}

/-- If two histories from positions of the same length coincide for all steps (up to a shift),
then the corresponding plays coincide. -/
lemma play_eq_of_hist_eq {p q : List A} {σ τ σ' τ' : List A → A}
    (hlen : q.length = p.length + 1)
    (h : ∀ n, hist p σ τ (n + 1) = hist q σ' τ' n) :
    play p σ τ = play q σ' τ' := by
  funext i
  rw [play, h i, play_eq_getD q σ' τ' i i (by omega)]

/-- If it is player I's turn at `p` and he wins from `p ++ [a]`, then he wins from `p`. -/
lemma WinI_of_succ_even {p : List A} (hp : Even p.length) {a : A}
    (h : WinI W (p ++ [a])) : WinI W p := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun l => if l = p then a else σ l, fun τ => ?_⟩
  have key : ∀ n, hist p (fun l => if l = p then a else σ l) τ (n + 1) = hist (p ++ [a]) σ τ n := by
    intro n
    induction n with
    | zero => simp [hist_succ, hp]
    | succ n ih =>
      rw [hist_succ, ih, hist_succ]
      have hlen : (hist (p ++ [a]) σ τ n).length = p.length + 1 + n := by
        rw [hist_length]; simp
      have hne : hist (p ++ [a]) σ τ n ≠ p := by
        intro hcon
        rw [hcon] at hlen; omega
      simp [hne]
  rw [play_eq_of_hist_eq (by simp) key]
  exact hσ τ

/-- If it is player II's turn at `p` and player I wins from every successor position,
then player I wins from `p`. -/
lemma WinI_of_forall_succ_odd {p : List A} (hp : ¬ Even p.length)
    (h : ∀ a : A, WinI W (p ++ [a])) : WinI W p := by
  choose f hf using h
  refine ⟨fun l => if p.length < l.length then f (l.getD p.length (Classical.arbitrary A)) l
      else Classical.arbitrary A, fun τ => ?_⟩
  set σ : List A → A := fun l => if p.length < l.length then
      f (l.getD p.length (Classical.arbitrary A)) l else Classical.arbitrary A with hσdef
  set a := τ p with ha
  have key : ∀ n, hist p σ τ (n + 1) = hist (p ++ [a]) (f a) τ n := by
    intro n
    induction n with
    | zero => simp [hist_succ, hp, ha]
    | succ n ih =>
      rw [hist_succ, ih, hist_succ]
      have hlen : (hist (p ++ [a]) (f a) τ n).length = p.length + 1 + n := by
        rw [hist_length]; simp
      have hpre : (p ++ [a]) <+: hist (p ++ [a]) (f a) τ n := prefix_hist _ _ _ _
      have hget : (hist (p ++ [a]) (f a) τ n).getD p.length (Classical.arbitrary A) = a := by
        rw [getD_of_prefix hpre p.length (by simp) _]
        simp [List.getD]
      have hs : σ (hist (p ++ [a]) (f a) τ n) = f a (hist (p ++ [a]) (f a) τ n) := by
        rw [hσdef]
        simp only [hlen, hget, if_pos (by omega : p.length < p.length + 1 + n)]
      rw [hs]
  rw [play_eq_of_hist_eq (by simp) key]
  exact hf a τ

/-- If every sequence extending the position `p` is winning for player I, then player I
wins from `p`. -/
lemma WinI_of_all_extensions {p : List A}
    (h : ∀ y : ℕ → A, (∀ i, i < p.length → y i = p.getD i (Classical.arbitrary A)) → y ∈ W) :
    WinI W p := by
  refine ⟨fun _ => Classical.arbitrary A, fun τ => ?_⟩
  exact h _ (fun i hi => play_eq_of_lt_length p _ τ i hi)

end Steps

/-- Openness of `W` in the product topology (with `A` discrete) means that membership in
`W` is decided by a finite initial segment. -/
lemma exists_prefix_subset_of_isOpen [TopologicalSpace A] [DiscreteTopology A]
    {W : Set (ℕ → A)} (hW : IsOpen W) {x : ℕ → A} (hx : x ∈ W) :
    ∃ n, ∀ y : ℕ → A, (∀ i, i < n → y i = x i) → y ∈ W := by
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW x hx
  refine ⟨(I.sup id) + 1, fun y hy => ?_⟩
  apply hsub
  intro a ha
  have h1 : (id a) ≤ I.sup id := Finset.le_sup ha
  simp only [id] at h1
  have hya : y a = x a := hy a (by omega)
  rw [hya]
  exact (hu a ha).2

/-- **The Gale–Stewart theorem**: every open game is determined.

Player I moves at the even indices, player II at the odd ones, and player I wins a play
`x : ℕ → A` iff `x ∈ W`.  If the payoff set `W` is open in the product topology (`A` being
discrete), then either player I has a winning strategy, or player II has one. -/
theorem Gale_Stewart_open {A : Type*} [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : List A → A, ∀ τ : List A → A, play [] σ τ ∈ W) ∨
    (∃ τ : List A → A, ∀ σ : List A → A, play [] σ τ ∉ W) := by
  by_cases hnil : WinI W ([] : List A)
  · exact Or.inl hnil
  refine Or.inr ?_
  -- Player II's strategy: always move to a position which is not winning for player I.
  set τ : List A → A := fun l =>
    if h : ∃ a : A, ¬ WinI W (l ++ [a]) then h.choose else Classical.arbitrary A with hτdef
  refine ⟨τ, fun σ hmem => ?_⟩
  -- Every position reached along the resulting play is not winning for player I.
  have key : ∀ n, ¬ WinI W (hist ([] : List A) σ τ n) := by
    intro n
    induction n with
    | zero => simpa using hnil
    | succ n ih =>
      rw [hist_succ]
      set L := hist ([] : List A) σ τ n with hL
      by_cases hev : Even L.length
      · simp only [hev, if_pos]
        intro hcon
        exact ih (WinI_of_succ_even hev hcon)
      · simp only [hev, if_false]
        have hex : ∃ a : A, ¬ WinI W (L ++ [a]) := by
          by_contra hcon
          push_neg at hcon
          exact ih (WinI_of_forall_succ_odd hev hcon)
        have hchoice : τ L = hex.choose := by rw [hτdef]; simp [dif_pos hex]
        rw [hchoice]
        exact hex.choose_spec
  -- If the play were won by player I, some finite initial segment would already be winning.
  obtain ⟨n, hn⟩ := exists_prefix_subset_of_isOpen hW hmem
  refine key n ?_
  apply WinI_of_all_extensions
  intro y hy
  apply hn
  intro i hi
  have hlen : (hist ([] : List A) σ τ n).length = n := by rw [hist_length]; simp
  rw [hy i (by omega), play_eq_getD ([] : List A) σ τ i n (by simpa using hi)]

end Frontier

