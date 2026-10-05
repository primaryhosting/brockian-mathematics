import RequestProject.QueryProg
import RequestProject.Aux

/-!
# An oracle `A` with `P^A = NP^A`

The oracle answers questions about its own relativized nondeterministic
computations.  This is well defined because the query `encodeQ i x t` is *longer*
than any string that can be queried during a computation of cost at most `t` on
input `x`, so the definition can be made by recursion on the length of the query.
-/

namespace CS

open Prog

/-- `AAux n z` is the value of the oracle at `z`, where `n` is the length of `z`;
the recursive calls are only made at strictly shorter strings. -/

theorem runs_appendConst (i : ℕ) (s : Str) (r : Regs) :
    Runs O (appendConst i s) r (Function.update r i (r i ++ s)) (s.length + 1) := by
  induction s generalizing r with
  | nil =>
      refine (runs_done r).congr ?_
      simp
  | cons b s ih =>
      have h1 : Runs O (Prog.appendBit i b) r (Function.update r i (r i ++ [b])) 1 :=
        runs_appendBit i b r
      have h2 := ih (r := Function.update r i (r i ++ [b]))
      refine ((h1.seq h2).congr ?_).mono ?_
      · funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_apply, hj]
      · simp
        omega

/-- The loop `while ctr ≠ [] do dst := dst ++ src; ctr := tail ctr`. -/
