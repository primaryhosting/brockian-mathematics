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

theorem NPClass_oracleA_subset_PClass : NPClass oracleA ⊆ PClass oracleA := by
  rintro L ⟨p, m, hL⟩
  obtain ⟨i, rfl⟩ := progOf_surjective p
  obtain ⟨m', hm'⟩ := polyBdd_le_pow (polyBdd_qCost i m)
  refine ⟨queryProg i m, m', noGuess_queryProg i m, ?_, ?_⟩
  · intro O' x
    obtain ⟨cfg, nn, hnn, hex, -⟩ := exec_queryProg O' i m x []
    exact ⟨cfg, nn, _, le_trans hnn (hm' x.length), hex⟩
  · intro x
    obtain ⟨cfg, nn, hnn, hex, hiff⟩ := exec_queryProg oracleA i m x []
    rw [hL x]
    constructor
    · intro h
      exact ⟨cfg, nn, _, le_trans hnn (hm' x.length), hex,
        hiff.2 ((oracleA_query i m x).2 h)⟩
    · rintro ⟨cfg2, n2, qs2, hn2, hex2, hacc2⟩
      obtain ⟨rfl, -, -⟩ := hex2.det cfg nn _ hex (noGuess_queryProg i m)
      exact (oracleA_query i m x).1 (hiff.1 hacc2)

/-- **First half of Baker–Gill–Solovay**: there is an oracle relative to which
`P` and `NP` coincide. -/
