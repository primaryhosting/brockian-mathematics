import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem reduce_cons_of_isReduced {x : α × Bool} {L : List (α × Bool)} (h : IsReduced L) :
    reduce (x :: L) = if L.head? = some (x.1, !x.2) then L.tail else x :: L := by
  rw [FreeGroup.reduce.cons, h.reduce_eq]
  cases L with
  | nil => simp
  | cons hd tl =>
    have hiff : (x.1 = hd.1 ∧ x.2 = !hd.2) ↔ (hd = (x.1, !x.2)) := by
      obtain ⟨x1, x2⟩ := x
      obtain ⟨h1, h2⟩ := hd
      simp only [Prod.mk.injEq]
      cases x2 <;> cases h2 <;> simp [eq_comm]
    show (if x.1 = hd.1 ∧ x.2 = !hd.2 then tl else x :: hd :: tl) = _
    by_cases hx : hd = (x.1, !x.2)
    · rw [if_pos (hiff.2 hx)]
      simp [hx]
    · rw [if_neg (fun hc => hx (hiff.1 hc))]
      simp [hx]

/-- Multiplying a reduced word by a single letter on the left. -/
