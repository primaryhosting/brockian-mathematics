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
