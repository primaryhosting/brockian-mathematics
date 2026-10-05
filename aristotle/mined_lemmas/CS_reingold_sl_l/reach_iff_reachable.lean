/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Graphs presented by neighbour maps -/

variable {n D k : ℕ}

/-- `walk nbr v w j` is the vertex reached from `v` after following the first `j`
directions of the direction sequence `w` in the `D`-regular graph given by the
neighbour map `nbr`. -/

theorem reach_iff_reachable [NeZero D] (nbr : Fin n → Fin D → Fin n)
    (hsym : ∀ (v : Fin n) (e : Fin D), ∃ e' : Fin D, nbr (nbr v e) e' = v) (s t : Fin n) :
    Reach nbr s t ↔ (ofNbr nbr).Reachable s t := by
  rw [reach_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c _ hstep ih =>
        rcases eq_or_ne b c with rfl | hne
        · exact ih
        · exact ih.trans (SimpleGraph.Adj.reachable
            (show (ofNbr nbr).Adj b c from ⟨hne, Or.inl hstep⟩))
  · rintro ⟨w⟩
    induction w with
    | nil => exact Relation.ReflTransGen.refl
    | cons hadj _ ih =>
        refine Relation.ReflTransGen.head ?_ ih
        rcases hadj.2 with h | ⟨e, he⟩
        · exact h
        · obtain ⟨e', he'⟩ := hsym _ e
          exact ⟨e', by rw [he] at he'; exact he'⟩

/-! ## Branching programs

A *branching program* is the standard non-uniform model of space-bounded computation:
a program with `length` levels whose memory at each level is a state in the finite type
`S`.  At each level the program reads one position of the (read-only) input, chosen as a
function of the current state, and updates its state.  Its *size* is the number of nodes,
`length * card S`; a program of size `M` uses `log₂ M` bits of memory, so
*polynomial size = logarithmic space*. -/

structure BP (Q A S : Type) where
  /-- Number of levels of the program. -/
  length : ℕ
  /-- Initial state. -/
  start : S
  /-- Which input position is read at a given level and state. -/
  query : ℕ → S → Q
  /-- State transition, given the level, the state and the answer of the query. -/
  next : ℕ → S → A → S
  /-- Accepting states. -/
  accept : S → Bool

variable {Q A S : Type}

/-- The state of `P` on input `input` after `i` levels. -/
