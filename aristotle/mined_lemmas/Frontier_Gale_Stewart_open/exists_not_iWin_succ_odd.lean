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
