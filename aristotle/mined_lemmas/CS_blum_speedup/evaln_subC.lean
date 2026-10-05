/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.CodeToolkit

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Summary

We work in Mathlib's standard model of computation: programs are
`Nat.Partrec.Code`s, and the running time of a program `c` on an input `n` is
`CS.time c n`, the least step bound `k` for which Mathlib's step-indexed
interpreter `Nat.Partrec.Code.evaln k c n` returns a value.  (This is a Blum
complexity measure: it is defined exactly when `c.eval n` converges, and the
predicate `time c n ≤ k` is decidable.)

The main theorem `CS.blum_speedup` says: for every computable, monotone
"speed-up factor" `T` there is a computable function `f` such that **no**
program for `f` is optimal — given any program `c` computing `f` one can
produce another program `c'` computing the *same* function `f` which, on
infinitely many inputs, is faster than `c` by more than the factor `T`:
`T (time c' n) < time c n`.

The corollary `CS.no_fastest_algorithm` states the headline consequence: the
problem `f` has no fastest algorithm, not even in the "almost everywhere"
sense.

## Relation to Blum's original theorem

Blum's speed-up theorem produces speed-ups that hold for *almost every* input.
The theorem proved here gives speed-ups on an *infinite* set of inputs (an
entire column `{Nat.pair e j | j}`, where `e` is the index of the program being
sped up).  This is weaker than the almost-everywhere form, but it is already
enough for the headline statement "there are problems with no fastest
algorithm": an almost-everywhere optimal program would in particular be at
least as fast as every competitor on all but finitely many inputs, which
`CS.no_fastest_algorithm` refutes.

The construction is a direct diagonalisation.  `diagF T n` simulates the
program coded by `n.unpair.1` on the input `n` for `bnd T n` steps and outputs
something different if that simulation converges.  Hence a program `c`
computing `diagF T` must take more than `bnd T n` steps on every input of its
own column, and on that column `diagF T` is identically `0`.  The competitor
`patch c (encode c)` answers `0` on that column (using an explicitly built
equality test whose running time is polynomially bounded) and defers to `c`
everywhere else.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Running time of a program -/

/-- The running time of the program `c` on input `n`: the least step bound
under which Mathlib's step-indexed interpreter produces an output.  (It is `0`
when the computation diverges.) -/

theorem evaln_subC : ∀ {N a b k : ℕ}, a ≤ N → b ≤ N → (2 * N + 2) ^ 4 + N + b ≤ k →
    evaln (k + 1) subC (Nat.pair a b) = some (a - b)
  | N, a, 0, k, haN, _, h => by
      have hb : Nat.pair a 0 ≤ (2 * N + 2) ^ 4 := pair_le_quart haN (Nat.zero_le _)
      exact evaln_prec_zero' (by omega) (evaln_id' (by omega))
  | N, a, b + 1, k, haN, hbN, h => by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hIH : evaln (k' + 1) subC (Nat.pair a b) = some (a - b) :=
        evaln_subC (N := N) haN (by omega) (by omega)
      have hpmi : Nat.pair b (a - b) ≤ (2 * N + 1) ^ 2 := pair_le_sq (by omega) (by omega)
      have hz : Nat.pair a (Nat.pair b (a - b)) ≤ (2 * N + 2) ^ 4 := pair_nest_le haN hpmi
      have hab : Nat.pair a (b + 1) ≤ (2 * N + 2) ^ 4 := pair_le_quart haN hbN
      have hb4 : (2 * N + 1) ^ 2 ≤ (2 * N + 2) ^ 4 := sq_le_quart N
      refine evaln_prec_succ' (k := k' + 1) (by omega) hIH ?_
      have hr1 : evaln (k' + 1 + 1) right (Nat.pair a (Nat.pair b (a - b)))
          = some (Nat.pair b (a - b)) := by
        have := evaln_right' (k := k' + 1) (n := Nat.pair a (Nat.pair b (a - b))) (by omega)
        simpa using this
      have hr2 : evaln (k' + 1 + 1) right (Nat.pair b (a - b)) = some (a - b) := by
        have := evaln_right' (k := k' + 1) (n := Nat.pair b (a - b)) (by omega)
        simpa using this
      have hrr : evaln (k' + 1 + 1) (comp right right) (Nat.pair a (Nat.pair b (a - b)))
          = some (a - b) := evaln_comp' (by omega) hr1 hr2
      have hp : evaln (k' + 1 + 1) pred1C (a - b) = some (a - (b + 1)) := by
        have h5 : a - b - 1 = a - (b + 1) := by omega
        have := evaln_pred1C (N := N) (x := a - b) (k := k' + 1) (by omega) (by omega)
        rwa [h5] at this
      exact evaln_comp' (by omega) hrr hp

