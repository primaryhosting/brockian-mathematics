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

theorem encodeQ_inj {i i' t t' : ℕ} {x x' : Str} (h : encodeQ i x t = encodeQ i' x' t') :
    i = i' ∧ x = x' ∧ t = t' := by
  simp only [encodeQ, List.append_assoc, List.singleton_append] at h
  obtain ⟨ht, h2⟩ := replicate_true_inj h
  obtain ⟨hi, hx⟩ := replicate_true_inj h2
  exact ⟨hi, hx, ht⟩

/-- `queryProg i m`: build the query string in register `2`, ask the oracle, and
put the answer in the output register `1`. -/
