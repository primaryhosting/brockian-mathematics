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

theorem oracleA_query (i m : ℕ) (x : Str) :
    oracleA (encodeQ i x ((x.length + 2) ^ m)) ↔
      ∃ cert, AcceptsWithin oracleA (progOf i) x cert ((x.length + 2) ^ m) := by
  set t := (x.length + 2) ^ m with ht
  have hlen : (encodeQ i x t).length = t + 1 + i + 1 + x.length := encodeQ_length i x t
  have hN : x.length + t < (encodeQ i x t).length := by rw [hlen]; omega
  rw [show oracleA (encodeQ i x t) = AAux (encodeQ i x t).length (encodeQ i x t) from rfl,
    AAux_iff]
  constructor
  · rintro ⟨i', x', t', heq, hrun⟩
    obtain ⟨rfl, rfl, rfl⟩ := encodeQ_inj heq.symm
    exact (acceptsWithin_short_iff _ _ _ _ hN).1 hrun
  · intro h
    exact ⟨i, x, t, rfl, (acceptsWithin_short_iff i x t _ hN).2 h⟩

/-- Every language in `NP^A` is in `P^A`: a single query to `A` decides it. -/
