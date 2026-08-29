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

theorem polyBdd_pow {f : ℕ → ℕ} (hf : PolyBdd f) (m : ℕ) : PolyBdd (fun n => f n ^ m) := by
  induction m with
  | zero => simpa using polyBdd_const 1
  | succ m ih =>
      have := polyBdd_mul ih hf
      refine polyBdd_mono (fun n => ?_) this
      rw [pow_succ]

/-- Every polynomially bounded function is bounded by `(n + 2) ^ m` for some `m`;
this lets us normalise polynomial time bounds. -/
