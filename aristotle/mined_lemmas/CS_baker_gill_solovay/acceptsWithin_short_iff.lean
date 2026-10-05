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

theorem acceptsWithin_short_iff (i : ℕ) (x : Str) (t N : ℕ) (hN : x.length + t < N) :
    (∃ cert, AcceptsWithin (fun y => y.length < N ∧ oracleA y) (progOf i) x cert t) ↔
      (∃ cert, AcceptsWithin oracleA (progOf i) x cert t) := by
  constructor
  · rintro ⟨cert, cfg, n, qs, hn, hex, hacc⟩
    refine ⟨cert, cfg, n, qs, hn, hex.locality ?_, hacc⟩
    intro s hs
    have hlen : s.length ≤ x.length + n := query_len_bound hex s hs
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  · rintro ⟨cert, cfg, n, qs, hn, hex, hacc⟩
    refine ⟨cert, cfg, n, qs, hn, hex.locality ?_, hacc⟩
    intro s hs
    have hlen : s.length ≤ x.length + n := query_len_bound hex s hs
    exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩

/-- The defining property of `A`. -/
