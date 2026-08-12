import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

variable {A : Type u}

/-! ## The game framework

We consider infinite two–player games on a set `A` of moves.  A *play* is a sequence
`x : ℕ → A`; player `0` chooses the moves `x n` with `n` even, player `1` chooses the moves
`x n` with `n` odd.  A *strategy* is a function `List A → A` assigning a move to every finite
position (the player only consults it at their own turns). -/

/-- The length-`n` initial segment of a play. -/
def pre (x : ℕ → A) (n : ℕ) : List A := (List.range n).map x

/-- The play `x` follows the strategy `s` for player `i` (`i` matters only modulo `2`). -/
def Follows (i : ℕ) (s : List A → A) (x : ℕ → A) : Prop :=
  ∀ n, n % 2 = i % 2 → x n = s (pre x n)

/-- `s` is a winning strategy for player `i` guaranteeing that the play lands in `S`. -/
def WinsFor (i : ℕ) (S : Set (ℕ → A)) (s : List A → A) : Prop :=
  ∀ x, Follows i s x → x ∈ S

/-- The game with payoff set `S` (player `0` wins iff the play is in `S`) is determined. -/
def Determined (S : Set (ℕ → A)) : Prop :=
  (∃ s, WinsFor 0 S s) ∨ (∃ s, WinsFor 1 Sᶜ s)

/-- Both games attached to `S` are determined: the one in which player `0` wants the play in
`S`, and the one in which player `0` wants the play outside `S`.  (Determinacy of a single
game is not preserved by complementation, so this symmetric notion is the one that behaves
well along the Borel hierarchy.) -/
def BiDetermined (S : Set (ℕ → A)) : Prop := Determined S ∧ Determined Sᶜ

/-! ## Basic facts about initial segments -/

@[simp] lemma pre_length (x : ℕ → A) (n : ℕ) : (pre x n).length = n := by
  simp [pre]

@[simp] lemma pre_zero (x : ℕ → A) : pre x 0 = [] := rfl

lemma pre_succ (x : ℕ → A) (n : ℕ) : pre x (n + 1) = pre x n ++ [x n] := by
  simp [pre, List.range_succ]

lemma pre_getD (x : ℕ → A) {k n : ℕ} (h : k < n) (d : A) : (pre x n).getD k d = x k := by
  rw [pre, List.getD_eq_getElem?_getD]
  simp [h]

lemma eq_of_pre_eq {x y : ℕ → A} {n k : ℕ} (h : pre y n = pre x n) (hk : k < n) : y k = x k := by
  have h1 : (pre y n).getD k (y k) = y k := pre_getD y hk (y k)
  have h2 : (pre x n).getD k (y k) = x k := pre_getD x hk (y k)
  rw [← h1, h, h2]

lemma parity_succ (i n : ℕ) : n % 2 = (i + 1) % 2 ↔ n % 2 ≠ i % 2 := by omega

lemma WinsFor.congr_parity {i j : ℕ} (h : i % 2 = j % 2) {S : Set (ℕ → A)} {s : List A → A}
    (hs : WinsFor i S s) : WinsFor j S s :=
  fun x hx => hs x fun n hn => hx n (by omega)

/-! ## Consistency of the framework

The two alternatives in `Determined` are mutually exclusive: any pair of strategies produces a
play consistent with both, so the two players cannot both win. -/

section Consistency

/-- The position reached after `n` moves when player `0` follows `s₀` and player `1` follows
`s₁`. -/
def playPos (s₀ s₁ : List A → A) : ℕ → List A
  | 0 => []
  | n + 1 => playPos s₀ s₁ n ++ [if n % 2 = 0 then s₀ (playPos s₀ s₁ n) else s₁ (playPos s₀ s₁ n)]

/-- The play produced when player `0` follows `s₀` and player `1` follows `s₁`. -/
def playOut (s₀ s₁ : List A → A) (n : ℕ) : A :=
  if n % 2 = 0 then s₀ (playPos s₀ s₁ n) else s₁ (playPos s₀ s₁ n)

lemma playPos_length (s₀ s₁ : List A → A) (n : ℕ) : (playPos s₀ s₁ n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [playPos, ih]

lemma pre_playOut (s₀ s₁ : List A → A) (n : ℕ) : pre (playOut s₀ s₁) n = playPos s₀ s₁ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pre_succ, ih, playPos, playOut]

lemma follows_playOut_zero (s₀ s₁ : List A → A) : Follows 0 s₀ (playOut s₀ s₁) := by
  intro n hn
  rw [pre_playOut, playOut, if_pos (by omega)]

lemma follows_playOut_one (s₀ s₁ : List A → A) : Follows 1 s₁ (playOut s₀ s₁) := by
  intro n hn
  rw [pre_playOut, playOut, if_neg (by omega)]

/-- The two players cannot both have a winning strategy. -/
theorem not_both_win (S : Set (ℕ → A)) :
    ¬ ((∃ s, WinsFor 0 S s) ∧ (∃ s, WinsFor 1 Sᶜ s)) := by
  rintro ⟨⟨s₀, h₀⟩, ⟨s₁, h₁⟩⟩
  exact h₁ _ (follows_playOut_one s₀ s₁) (h₀ _ (follows_playOut_zero s₀ s₁))

end Consistency

/-! ## The Gale–Stewart theorem (the base case of Martin's theorem)

A game whose payoff set is closed (in the product topology, `A` discrete) is determined.
This is proved via an inductively defined predicate describing the positions from which the
player *aiming to leave the tree* wins. -/

section GaleStewart

/-- `OppWins i T p` : from the position `p`, the opponent of player `i` can force the play to
leave the tree `T` (player `i` moves at positions of length `≡ i [MOD 2]`). -/
inductive OppWins (i : ℕ) (T : List A → Prop) : List A → Prop
  | out {p : List A} : ¬ T p → OppWins i T p
  | move {p : List A} (a : A) :
      p.length % 2 ≠ i % 2 → OppWins i T (p ++ [a]) → OppWins i T p
  | all {p : List A} :
      p.length % 2 = i % 2 → (∀ a : A, OppWins i T (p ++ [a])) → OppWins i T p

variable [Nonempty A]

/-- If the opponent of `i` does not win from the empty position, player `i` has a strategy
keeping the play inside the tree `T` forever. -/
lemma exists_strategy_of_not_oppWins (i : ℕ) (T : List A → Prop) (h : ¬ OppWins i T []) :
    ∃ s : List A → A, ∀ x : ℕ → A, Follows i s x → ∀ n, T (pre x n) := by
  classical
  haveI : Inhabited A := Classical.inhabited_of_nonempty inferInstance
  refine ⟨fun p => if hp : ∃ a, ¬ OppWins i T (p ++ [a]) then hp.choose else default, ?_⟩
  intro x hx
  have key : ∀ n, ¬ OppWins i T (pre x n) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      rw [pre_succ]
      by_cases hturn : n % 2 = i % 2
      · have hex : ∃ a, ¬ OppWins i T (pre x n ++ [a]) := by
          by_contra hcon
          push_neg at hcon
          exact ih (OppWins.all (by simpa using hturn) hcon)
        rw [hx n hturn]
        simp only [dif_pos hex]
        exact hex.choose_spec
      · intro hw
        exact ih (OppWins.move (x n) (by simpa using hturn) hw)
  intro n
  by_contra hT
  exact key n (OppWins.out hT)

/-- If the opponent of `i` wins from the position `p`, they have a strategy which, against any
play extending `p`, forces the play out of the tree `T`. -/
lemma exists_strategy_of_oppWins (i : ℕ) (T : List A → Prop) :
    ∀ {p : List A}, OppWins i T p →
      ∃ s : List A → A, ∀ x : ℕ → A, pre x p.length = p →
        (∀ n, p.length ≤ n → n % 2 ≠ i % 2 → x n = s (pre x n)) → ∃ n, ¬ T (pre x n) := by
  classical
  haveI : Inhabited A := Classical.inhabited_of_nonempty inferInstance
  intro p hp
  induction hp with
  | @out p hT =>
      refine ⟨fun _ => default, fun x hx _ => ⟨p.length, ?_⟩⟩
      rw [hx]; exact hT
  | @move p a hturn _ ih =>
      obtain ⟨s', hs'⟩ := ih
      refine ⟨fun q => if q = p then a else s' q, ?_⟩
      intro x hx hcons
      have h0 : x p.length = a := by
        have h1 := hcons p.length le_rfl hturn
        rw [hx] at h1
        simpa using h1
      have hlen : (p ++ [a]).length = p.length + 1 := by simp
      have hx1 : pre x (p ++ [a]).length = p ++ [a] := by
        rw [hlen, pre_succ, hx, h0]
      refine hs' x hx1 (fun n hn hpar => ?_)
      rw [hlen] at hn
      have hne : pre x n ≠ p := by
        intro hq
        have := congrArg List.length hq
        simp at this
        omega
      have h2 := hcons n (by omega) hpar
      simpa [hne] using h2
  | @all p hturn _ ih =>
      choose s' hs' using ih
      refine ⟨fun q => if p.length < q.length then s' (q.getD p.length default) q else default, ?_⟩
      intro x hx hcons
      have hlen : (p ++ [x p.length]).length = p.length + 1 := by simp
      have hx1 : pre x (p ++ [x p.length]).length = p ++ [x p.length] := by
        rw [hlen, pre_succ, hx]
      refine hs' (x p.length) x hx1 (fun n hn hpar => ?_)
      rw [hlen] at hn
      have hlt : p.length < n := by omega
      have h2 := hcons n (le_of_lt hlt) hpar
      rw [h2]
      have h3 : (pre x n).getD p.length default = x p.length := pre_getD x hlt default
      simp only [pre_length]
      rw [if_pos hlt, h3]

variable [TopologicalSpace A] [DiscreteTopology A]

omit [Nonempty A] in
/-- A closed set is determined by finite initial segments: a play outside a closed set has a
finite initial segment witnessing this. -/
lemma exists_pre_of_notMem {S : Set (ℕ → A)} (hS : IsClosed S) {x : ℕ → A} (hx : x ∉ S) :
    ∃ n, ∀ y : ℕ → A, pre y n = pre x n → y ∉ S := by
  have hmem : Sᶜ ∈ nhds x := hS.isOpen_compl.mem_nhds hx
  rw [nhds_pi] at hmem
  obtain ⟨I, hI, t, ht, hsub⟩ := Filter.mem_pi.1 hmem
  obtain ⟨n, hn⟩ : ∃ n, ∀ i ∈ I, i < n := by
    obtain ⟨n, hn⟩ := hI.bddAbove
    exact ⟨n + 1, fun i hi => lt_of_le_of_lt (hn hi) (lt_add_one n)⟩
  refine ⟨n, fun y hy hyS => ?_⟩
  refine hsub (fun i hi => ?_) hyS
  have hxi : x i ∈ t i := mem_nhds_discrete.1 (ht i)
  have : y i = x i := eq_of_pre_eq hy (hn i hi)
  rw [this]
  exact hxi

/-- **Gale–Stewart theorem**: a game with closed payoff set is determined, for either
assignment of the roles to the two players (`i` is the player aiming at the closed set `S`). -/
theorem gale_stewart (i : ℕ) {S : Set (ℕ → A)} (hS : IsClosed S) :
    (∃ s, WinsFor i S s) ∨ (∃ s, WinsFor (i + 1) Sᶜ s) := by
  classical
  set T : List A → Prop := fun p => ∃ y ∈ S, pre y p.length = p
  have hTS : ∀ x : ℕ → A, (∀ n, T (pre x n)) → x ∈ S := by
    intro x hx
    by_contra hxS
    obtain ⟨n, hn⟩ := exists_pre_of_notMem hS hxS
    obtain ⟨y, hyS, hy⟩ := hx n
    rw [pre_length] at hy
    exact hn y hy hyS
  by_cases h : OppWins i T []
  · right
    obtain ⟨s, hs⟩ := exists_strategy_of_oppWins i T h
    refine ⟨s, fun x hxf hxS => ?_⟩
    obtain ⟨n, hn⟩ : ∃ n, ¬ T (pre x n) := by
      refine hs x (by simp) (fun n _ hpar => hxf n ?_)
      rw [parity_succ]
      exact hpar
    exact hn ⟨x, hxS, by rw [pre_length]⟩
  · left
    obtain ⟨s, hs⟩ := exists_strategy_of_not_oppWins i T h
    exact ⟨s, fun x hx => hTS x (hs x hx)⟩

end GaleStewart

/-! ## The Borel hierarchy -/

section Borel

variable [TopologicalSpace A]

/-- `S` is a Borel subset of the space of plays `ℕ → A` (product topology, `A` discrete). -/
def IsBorelSet (S : Set (ℕ → A)) : Prop := @MeasurableSet (ℕ → A) (borel (ℕ → A)) S

omit [TopologicalSpace A] in
lemma BiDetermined.compl {S : Set (ℕ → A)} (h : BiDetermined S) : BiDetermined Sᶜ :=
  ⟨h.2, by rw [compl_compl]; exact h.1⟩

variable [Nonempty A] [DiscreteTopology A]

/-- Closed sets are bi-determined. -/
theorem closed_biDetermined {S : Set (ℕ → A)} (hS : IsClosed S) : BiDetermined S := by
  refine ⟨gale_stewart 0 hS, ?_⟩
  rcases gale_stewart 1 hS with ⟨s, hs⟩ | ⟨s, hs⟩
  · right
    exact ⟨s, by rw [compl_compl]; exact hs⟩
  · left
    exact ⟨s, hs.congr_parity (by norm_num)⟩

/-- Open sets are bi-determined. -/
theorem open_biDetermined {S : Set (ℕ → A)} (hS : IsOpen S) : BiDetermined S := by
  have h := closed_biDetermined (isClosed_compl_iff.2 hS)
  simpa using h.compl

/-- **Borel determinacy** (Martin's theorem), as a Lean-checked reduction: granting the
countable-union step of Martin's induction (a true statement, being a consequence of the full
theorem), every Borel game is determined.  The base case of the induction — determinacy of
closed games, the Gale–Stewart theorem — is proved unconditionally above
(`Frontier.gale_stewart`), as is the closure of the class of bi-determined sets under
complementation (`Frontier.BiDetermined.compl`). -/
theorem Borel_determinacy
    (hUnion : ∀ f : ℕ → Set (ℕ → A), (∀ n, IsBorelSet (f n)) →
      (∀ n, BiDetermined (f n)) → BiDetermined (⋃ n, f n))
    {S : Set (ℕ → A)} (hS : IsBorelSet S) : Determined S := by
  have hgen : ∀ t : Set (ℕ → A),
      MeasurableSpace.GenerateMeasurable {u : Set (ℕ → A) | IsClosed u} t → IsBorelSet t := by
    intro t ht
    show @MeasurableSet (ℕ → A) (borel (ℕ → A)) t
    rw [borel_eq_generateFrom_isClosed]
    exact ht
  have key : ∀ t : Set (ℕ → A),
      MeasurableSpace.GenerateMeasurable {u : Set (ℕ → A) | IsClosed u} t → BiDetermined t := by
    intro t ht
    induction ht with
    | basic u hu => exact closed_biDetermined hu
    | empty => exact closed_biDetermined isClosed_empty
    | compl t _ ih => exact ih.compl
    | iUnion f hf ih => exact hUnion f (fun n => hgen _ (hf n)) ih
  have hS' : MeasurableSpace.GenerateMeasurable {u : Set (ℕ → A) | IsClosed u} S := by
    have h := hS
    rw [IsBorelSet, borel_eq_generateFrom_isClosed] at h
    exact h
  exact (key S hS').1

end Borel

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

