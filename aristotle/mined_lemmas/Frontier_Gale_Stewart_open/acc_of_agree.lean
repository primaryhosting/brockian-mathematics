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

