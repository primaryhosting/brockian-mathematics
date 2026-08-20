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
namespace GaleStewart

variable {A : Type*} [Inhabited A]

/-- The initial segment of a play `f` of length `n`, padded with `default`. -/
def trunc (f : ℕ → A) (n : ℕ) : ℕ → A := fun i => if i < n then f i else default

/-- The play resulting from Player I using strategy `σ` (moving at even stages) and
Player II using strategy `τ` (moving at odd stages).  A strategy takes the stage number
and the history of the play so far (truncated, padded with `default`). -/
def play (σ τ : ℕ → (ℕ → A) → A) : ℕ → A
  | n => (if Even n then σ n else τ n) (fun i => if _h : i < n then play σ τ i else default)
decreasing_by omega

lemma play_eq (σ τ : ℕ → (ℕ → A) → A) (n : ℕ) :
    play σ τ n = (if Even n then σ n else τ n) (trunc (play σ τ) n) := by
  rw [play]; congr 1

lemma trunc_succ (f : ℕ → A) (n : ℕ) :
    trunc f (n + 1) = Function.update (trunc f n) n (f n) := by
  funext i
  by_cases h : i = n
  · subst h; simp [trunc]
  · rw [Function.update_of_ne h]
    simp only [trunc]
    by_cases h2 : i < n
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

lemma trunc_agree (f : ℕ → A) (n : ℕ) {i : ℕ} (h : i < n) : trunc f n i = f i := by
  simp [trunc, h]

variable (W : Set (ℕ → A))

/-- A position (a length `n` and a sequence `s`, of which only the first `n` entries matter)
is *good* for Player I when every play extending it lies in the payoff set `W`. -/
def Good (n : ℕ) (s : ℕ → A) : Prop := ∀ g : ℕ → A, (∀ i, i < n → g i = s i) → g ∈ W

/-- Given a move-choice function `c` for Player I, `Succ W c q p` says that `q` is a
successor position of the non-good position `p`: at even stages the move is the one
prescribed by `c`, at odd stages it is an arbitrary move of Player II. -/
def Succ (c : ℕ → (ℕ → A) → A) (q p : ℕ × (ℕ → A)) : Prop :=
  ¬ Good W p.1 p.2 ∧ q.1 = p.1 + 1 ∧
    (if Even p.1 then q.2 = Function.update p.2 p.1 (c p.1 p.2)
      else ∃ a : A, q.2 = Function.update p.2 p.1 a)

/-- Player I wins from the position `p` when there is a move-choice function `c` for which
the tree of plays following `c` from `p` and avoiding good positions is well-founded, i.e.
Player I can force reaching a good position in finitely many moves. -/
def IWin (p : ℕ × (ℕ → A)) : Prop := ∃ c : ℕ → (ℕ → A) → A, Acc (Succ W c) p

lemma acc_of_good {c : ℕ → (ℕ → A) → A} {p : ℕ × (ℕ → A)} (h : Good W p.1 p.2) :
    Acc (Succ W c) p :=
  Acc.intro _ (fun _ hy => absurd h hy.1)

/-- Accessibility is transferred between move-choice functions that agree on a set of
positions closed under taking successors. -/
lemma acc_of_agree {c c' : ℕ → (ℕ → A) → A} (P : ℕ × (ℕ → A) → Prop)
    (hP : ∀ p q, P p → Succ W c q p → P q)
    (hc : ∀ p : ℕ × (ℕ → A), P p → c p.1 p.2 = c' p.1 p.2) :
    ∀ p, Acc (Succ W c) p → P p → Acc (Succ W c') p := by
  intro p hacc
  induction hacc with
  | intro x _ ih =>
    intro hPx
    refine Acc.intro _ (fun y hy => ?_)
    have hy' : Succ W c y x := by
      obtain ⟨h1, h2, h3⟩ := hy
      refine ⟨h1, h2, ?_⟩
      by_cases he : Even x.1
      · rw [if_pos he] at h3 ⊢
        rw [hc x hPx]; exact h3
      · rw [if_neg he] at h3 ⊢; exact h3
    exact ih y hy' (hP x y hPx hy')

lemma not_good_of_not_iWin {p : ℕ × (ℕ → A)} (h : ¬ IWin W p) : ¬ Good W p.1 p.2 := by
  intro hg
  exact h ⟨fun _ _ => default, acc_of_good W hg⟩

/-- If Player I does not win from an even (Player I to move) position, then he does not win
from any of its successors. -/
lemma not_iWin_succ_even {p : ℕ × (ℕ → A)} (h : ¬ IWin W p) (he : Even p.1) (a : A) :
    ¬ IWin W (p.1 + 1, Function.update p.2 p.1 a) := by
  rintro ⟨c, hacc⟩
  set c' : ℕ → (ℕ → A) → A := fun m t => if m = p.1 then a else c m t with hc'
  have hchild : Acc (Succ W c') (p.1 + 1, Function.update p.2 p.1 a) := by
    refine acc_of_agree W (fun q => p.1 < q.1) ?_ ?_ _ hacc (by simp)
    · rintro q r hq ⟨-, h2, -⟩
      omega
    · intro q hq
      simp only [hc', if_neg (by omega : ¬ q.1 = p.1)]
  refine h ⟨c', Acc.intro _ (fun y hy => ?_)⟩
  obtain ⟨-, h2, h3⟩ := hy
  rw [if_pos he] at h3
  have : y = (p.1 + 1, Function.update p.2 p.1 a) := by
    have hcp : c' p.1 p.2 = a := by simp [hc']
    rw [hcp] at h3
    exact Prod.ext h2 h3
  rw [this]; exact hchild

/-- If Player I does not win from an odd (Player II to move) position, then Player II has a
move to a successor position from which Player I still does not win. -/
lemma exists_not_iWin_succ_odd {p : ℕ × (ℕ → A)} (h : ¬ IWin W p) (ho : ¬ Even p.1) :
    ∃ a : A, ¬ IWin W (p.1 + 1, Function.update p.2 p.1 a) := by
  by_contra hcon
  push_neg at hcon
  choose C hC using fun a : A => hcon a
  set c : ℕ → (ℕ → A) → A := fun m t => C (t p.1) m t with hc
  have key : ∀ a : A, Acc (Succ W c) (p.1 + 1, Function.update p.2 p.1 a) := by
    intro a
    refine acc_of_agree W (fun q => p.1 < q.1 ∧ q.2 p.1 = a) ?_ ?_ _ (hC a) ⟨by omega, by simp⟩
    · rintro q r ⟨hq1, hq2⟩ ⟨-, h2, h3⟩
      refine ⟨by omega, ?_⟩
      have hne : ¬ p.1 = q.1 := by omega
      by_cases he : Even q.1
      · rw [if_pos he] at h3
        rw [h3, Function.update_of_ne hne, hq2]
      · rw [if_neg he] at h3
        obtain ⟨b, hb⟩ := h3
        rw [hb, Function.update_of_ne hne, hq2]
    · rintro q ⟨-, hq2⟩
      simp only [hc, hq2]
  refine h ⟨c, Acc.intro _ (fun y hy => ?_)⟩
  obtain ⟨-, h2, h3⟩ := hy
  rw [if_neg ho] at h3
  obtain ⟨a, ha⟩ := h3
  have : y = (p.1 + 1, Function.update p.2 p.1 a) := Prod.ext h2 ha
  rw [this]; exact key a

/-- If Player I wins (in the sense of `IWin`) from the initial position, then the choice
function witnessing this is a winning strategy: every play following it reaches a good
position. -/
lemma exists_good_of_acc {c : ℕ → (ℕ → A) → A} (τ : ℕ → (ℕ → A) → A) :
    ∀ p : ℕ × (ℕ → A), Acc (Succ W c) p →
      ∀ n : ℕ, p = (n, trunc (play c τ) n) → ∃ m, Good W m (trunc (play c τ) m) := by
  intro p hacc
  induction hacc with
  | intro x _ ih =>
    intro n hn
    by_cases hg : Good W n (trunc (play c τ) n)
    · exact ⟨n, hg⟩
    · refine ih (n + 1, trunc (play c τ) (n + 1)) ?_ (n + 1) rfl
      subst hn
      refine ⟨hg, rfl, ?_⟩
      simp only
      by_cases he : Even n
      · rw [if_pos he, trunc_succ]
        congr 1
        rw [play_eq, if_pos he]
      · rw [if_neg he]
        exact ⟨play c τ n, trunc_succ _ _⟩

/-- Openness of the payoff set: any play in `W` has a finite initial segment all of whose
extensions lie in `W`. -/
lemma exists_good_of_isOpen [TopologicalSpace A] (hW : IsOpen W) {f : ℕ → A} (hf : f ∈ W) :
    ∃ n, Good W n (trunc f n) := by
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW f hf
  refine ⟨(I.sup id) + 1, ?_⟩
  intro g hg
  apply hsub
  intro i hi
  have hlt : i < (I.sup id) + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  rw [hg i hlt, trunc_agree f _ hlt]
  exact (hu i hi).2

end GaleStewart

/-- **Gale–Stewart theorem for open games.**  Two players alternately choose moves from a
(nonempty, discrete) set `A` of moves, Player I moving at even stages and Player II at odd
stages, producing an infinite play `f : ℕ → A`.  Player I wins if `f` belongs to the payoff
set `W`, which is assumed to be open in the product topology.  Then the game is determined:
either Player I has a strategy winning against every strategy of Player II, or Player II has
a strategy winning against every strategy of Player I. -/
theorem Gale_Stewart_open {A : Type*} [Inhabited A] [TopologicalSpace A] [DiscreteTopology A]
    (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : ℕ → (ℕ → A) → A, ∀ τ : ℕ → (ℕ → A) → A, GaleStewart.play σ τ ∈ W) ∨
      (∃ τ : ℕ → (ℕ → A) → A, ∀ σ : ℕ → (ℕ → A) → A, GaleStewart.play σ τ ∉ W) := by
  classical
  open GaleStewart in
  by_cases hI : IWin W (0, trunc (fun _ => default) 0)
  · obtain ⟨c, hacc⟩ := hI
    refine Or.inl ⟨c, fun τ => ?_⟩
    obtain ⟨m, hm⟩ := exists_good_of_acc W τ _ hacc 0 (by rfl)
    exact hm _ (fun i hi => (trunc_agree _ _ hi).symm)
  · refine Or.inr ⟨fun n t =>
      if h : ∃ a : A, ¬ IWin W (n + 1, Function.update t n a) then h.choose else default,
      fun σ => ?_⟩
    set τ : ℕ → (ℕ → A) → A := fun n t =>
      if h : ∃ a : A, ¬ IWin W (n + 1, Function.update t n a) then h.choose else default with hτ
    set f := play σ τ with hf
    have inv : ∀ n : ℕ, ¬ IWin W (n, trunc f n) := by
      intro n
      induction n with
      | zero => exact hI
      | succ n ih =>
        by_cases he : Even n
        · have := not_iWin_succ_even W (p := (n, trunc f n)) ih he (f n)
          rw [trunc_succ]
          exact this
        · have hex : ∃ a : A, ¬ IWin W (n + 1, Function.update (trunc f n) n a) :=
            exists_not_iWin_succ_odd W (p := (n, trunc f n)) ih he
          have hfn : f n = hex.choose := by
            rw [hf, play_eq, if_neg he, hτ]
            simp only [dif_pos hex]
          rw [trunc_succ, hfn]
          exact hex.choose_spec
    intro hmem
    obtain ⟨n, hn⟩ := exists_good_of_isOpen W hW hmem
    exact not_good_of_not_iWin W (inv n) hn

end Frontier

