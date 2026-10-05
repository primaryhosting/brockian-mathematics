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

/-- The finite position consisting of the first `n` moves of the play `x`. -/
def prefixOf (x : ℕ → A) (n : ℕ) : List A := (List.range n).map x

@[simp] lemma length_prefixOf (x : ℕ → A) (n : ℕ) : (prefixOf x n).length = n := by
  simp [prefixOf]

@[simp] lemma getElem_prefixOf (x : ℕ → A) (n i : ℕ) (h : i < (prefixOf x n).length) :
    (prefixOf x n)[i] = x i := by
  simp only [prefixOf, List.getElem_map, List.getElem_range]

lemma prefixOf_succ (x : ℕ → A) (n : ℕ) : prefixOf x (n + 1) = prefixOf x n ++ [x n] := by
  simp [prefixOf, List.range_succ]

/-- The infinite play `x` extends the finite position `p`. -/
def Extends (p : List A) (x : ℕ → A) : Prop := ∀ i (h : i < p.length), x i = p[i]

/-- A play `x` is consistent with the strategy `σ` of Player I (who moves at even stages)
from the position `p`. -/
def ConsistentI (σ : List A → A) (p : List A) (x : ℕ → A) : Prop :=
  Extends p x ∧ ∀ n, p.length ≤ n → Even n → x n = σ (prefixOf x n)

/-- A play `x` is consistent with the strategy `τ` of Player II (who moves at odd stages)
from the position `p`. -/
def ConsistentII (τ : List A → A) (p : List A) (x : ℕ → A) : Prop :=
  Extends p x ∧ ∀ n, p.length ≤ n → Odd n → x n = τ (prefixOf x n)

/-- `σ` is a winning strategy for Player I, from the position `p`, in the game with payoff `W`. -/
def WinningI (W : Set (ℕ → A)) (σ : List A → A) (p : List A) : Prop :=
  ∀ x, ConsistentI σ p x → x ∈ W

/-- `τ` is a winning strategy for Player II, from the position `p`, in the game with payoff `W`. -/
def WinningII (W : Set (ℕ → A)) (τ : List A → A) (p : List A) : Prop :=
  ∀ x, ConsistentII τ p x → x ∉ W

section Basic

lemma extends_append_singleton {p : List A} {a : A} {x : ℕ → A}
    (hp : Extends p x) (ha : x p.length = a) : Extends (p ++ [a]) x := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
  · rw [hp i h, List.getElem_append_left h]
  · subst h
    rw [ha]
    simp

end Basic

section NoWin

variable (W : Set (ℕ → A))

/-- If Player I has no winning strategy from an even-length position `p` (so it is Player I's
turn), then he has no winning strategy from any one-move extension of `p`. -/
lemma noWinI_of_moveI {p : List A} (hp : Even p.length)
    (h : ¬ ∃ σ : List A → A, WinningI W σ p) (a : A) :
    ¬ ∃ σ : List A → A, WinningI W σ (p ++ [a]) := by
  rintro ⟨σ, hσ⟩
  refine h ⟨fun q => if q.length = p.length then a else σ q, ?_⟩
  intro x hx
  obtain ⟨hext, hmove⟩ := hx
  have hxa : x p.length = a := by simpa using hmove p.length le_rfl hp
  refine hσ x ⟨extends_append_singleton hext hxa, ?_⟩
  intro n hn hne
  simp only [List.length_append, List.length_singleton] at hn
  rw [hmove n (by omega) hne]
  have hlen : ¬ ((prefixOf x n).length = p.length) := by
    simp only [length_prefixOf]; omega
  simp only [if_neg hlen]

/-- If Player I has no winning strategy from a position `p`, then there is a move `a` after
which Player I still has no winning strategy.  (Used at the positions where it is Player II's
turn: this is the move Player II will play.) -/
lemma exists_noWinI_of_moveII [Nonempty A] {p : List A}
    (h : ¬ ∃ σ : List A → A, WinningI W σ p) :
    ∃ a : A, ¬ ∃ σ : List A → A, WinningI W σ (p ++ [a]) := by
  by_contra hcon
  push_neg at hcon
  choose f hf using hcon
  refine h ⟨fun q => if hq : p.length < q.length then f q[p.length] q else Classical.arbitrary A,
    ?_⟩
  intro x hx
  obtain ⟨hext, hmove⟩ := hx
  refine hf (x p.length) x ⟨extends_append_singleton hext rfl, ?_⟩
  intro n hn hne
  simp only [List.length_append, List.length_singleton] at hn
  rw [hmove n (by omega) hne]
  have hlt : p.length < (prefixOf x n).length := by
    simp only [length_prefixOf]; omega
  simp only [dif_pos hlt, getElem_prefixOf]

end NoWin

/-- Openness of `W` in the product topology, in combinatorial form: every play in `W` has a
finite prefix all of whose extensions lie in `W`. -/
lemma exists_prefix_subset_of_isOpen [TopologicalSpace A] {W : Set (ℕ → A)} (hW : IsOpen W)
    {x : ℕ → A} (hx : x ∈ W) : ∃ n : ℕ, ∀ y : ℕ → A, (∀ i, i < n → y i = x i) → y ∈ W := by
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW x hx
  refine ⟨I.sup id + 1, fun y hy => hsub ?_⟩
  intro i hi
  have hmem : i ∈ I := Finset.mem_coe.mp hi
  have hle : i ≤ I.sup id := Finset.le_sup (f := id) hmem
  rw [hy i (by omega)]
  exact (hu i hmem).2

/-- **Gale–Stewart theorem**: every open game is determined.

Two players alternately choose elements of a nonempty set `A` of moves, Player I moving at the
even stages and Player II at the odd stages, producing a play `x : ℕ → A`.  Player I wins if
`x ∈ W`.  If the payoff set `W` is open in the product topology on `ℕ → A` (with `A` discrete),
then one of the two players has a winning strategy from the initial (empty) position. -/
theorem Gale_Stewart_open {A : Type*} [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : List A → A, WinningI W σ []) ∨ (∃ τ : List A → A, WinningII W τ []) := by
  by_cases hI : ∃ σ : List A → A, WinningI W σ []
  · exact Or.inl hI
  refine Or.inr ⟨fun q => if hq : ∃ a : A, ¬ ∃ σ : List A → A, WinningI W σ (q ++ [a]) then
    hq.choose else Classical.arbitrary A, ?_⟩
  intro x hx hxW
  obtain ⟨-, hmove⟩ := hx
  have key : ∀ n : ℕ, ¬ ∃ σ : List A → A, WinningI W σ (prefixOf x n) := by
    intro n
    induction n with
    | zero => simpa [prefixOf] using hI
    | succ n ih =>
      rw [prefixOf_succ]
      rcases Nat.even_or_odd n with hn | hn
      · exact noWinI_of_moveI W (by simpa using hn) ih (x n)
      · have hex := exists_noWinI_of_moveII W ih
        have hxn : x n = _ := hmove n (Nat.zero_le _) hn
        rw [hxn]
        simp only [dif_pos hex]
        exact hex.choose_spec
  obtain ⟨n, hn⟩ := exists_prefix_subset_of_isOpen hW hxW
  refine key n ⟨fun _ => Classical.arbitrary A, fun y hy => hn y (fun i hi => ?_)⟩
  have hi' : i < (prefixOf x n).length := by simpa using hi
  rw [hy.1 i hi', getElem_prefixOf x n i hi']

/-! ### The play generated by a pair of strategies

The following complements the theorem above: a pair of strategies always generates a play
consistent with both, so the two disjuncts of `Gale_Stewart_open` are mutually exclusive and
neither notion of "winning strategy" is vacuously satisfied. -/

section Play

variable (σ τ : List A → A)

/-- The position reached after `n` moves when Player I follows `σ` and Player II follows `τ`. -/
def runPos : ℕ → List A
  | 0 => []
  | n + 1 => runPos n ++ [if Even n then σ (runPos n) else τ (runPos n)]

@[simp] lemma length_runPos (n : ℕ) : (runPos σ τ n).length = n := by
  induction n with
  | zero => simp [runPos]
  | succ n ih => simp [runPos, ih]

/-- The play generated by the strategies `σ` and `τ`. -/
def playOf (n : ℕ) : A := (runPos σ τ (n + 1))[n]'(by simp)

lemma playOf_eq (n : ℕ) :
    playOf σ τ n = if Even n then σ (runPos σ τ n) else τ (runPos σ τ n) := by
  have h : (runPos σ τ (n + 1))[n]'(by simp) =
      (runPos σ τ n ++ [if Even n then σ (runPos σ τ n) else τ (runPos σ τ n)])[n]'(by simp) := by
    congr 1
  rw [playOf, h]
  simp

lemma prefixOf_playOf (n : ℕ) : prefixOf (playOf σ τ) n = runPos σ τ n := by
  induction n with
  | zero => simp [prefixOf, runPos]
  | succ n ih => rw [prefixOf_succ, ih, playOf_eq, runPos]

lemma consistentI_playOf : ConsistentI σ [] (playOf σ τ) := by
  refine ⟨fun i hi => absurd hi (by simp), fun n _ hn => ?_⟩
  rw [prefixOf_playOf, playOf_eq, if_pos hn]

lemma consistentII_playOf : ConsistentII τ [] (playOf σ τ) := by
  refine ⟨fun i hi => absurd hi (by simp), fun n _ hn => ?_⟩
  rw [prefixOf_playOf, playOf_eq, if_neg (Nat.not_even_iff_odd.mpr hn)]

/-- The two players cannot both have a winning strategy: determinacy is an exclusive
disjunction. -/
theorem not_winningI_and_winningII (W : Set (ℕ → A)) :
    ¬ (WinningI W σ [] ∧ WinningII W τ []) := by
  rintro ⟨hσ, hτ⟩
  exact hτ (playOf σ τ) (consistentII_playOf σ τ) (hσ (playOf σ τ) (consistentI_playOf σ τ))

end Play

end Frontier

