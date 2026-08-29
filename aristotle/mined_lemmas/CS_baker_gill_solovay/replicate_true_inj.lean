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

theorem replicate_true_inj {t t' : ℕ} {r r' : Str}
    (h : List.replicate t true ++ false :: r = List.replicate t' true ++ false :: r') :
    t = t' ∧ r = r' := by
  induction t generalizing t' with
  | zero =>
      cases t' with
      | zero => simpa using h
      | succ t' => simp [List.replicate_succ] at h
  | succ t ih =>
      cases t' with
      | zero => simp [List.replicate_succ] at h
      | succ t' =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨ht, hr⟩ := ih h
          exact ⟨by omega, hr⟩

