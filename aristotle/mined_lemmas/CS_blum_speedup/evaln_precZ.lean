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

theorem evaln_precZ : ∀ {N m k : ℕ}, m ≤ N → (2 * N + 2) ^ 4 + m ≤ k →
    evaln (k + 1) precZ (Nat.pair 0 m) = some (m - 1)
  | _, 0, k, _, _ => by
      refine evaln_prec_zero' (by norm_num [Nat.pair]) ?_
      exact evaln_zero' (Nat.zero_le _)
  | N, m + 1, k, hmN, h => by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hIH : evaln (k' + 1) precZ (Nat.pair 0 m) = some (m - 1) :=
        evaln_precZ (N := N) (by omega) (by omega)
      have hb1 : Nat.pair m (m - 1) ≤ (2 * N + 1) ^ 2 := pair_le_sq (by omega) (by omega)
      have hb2 : Nat.pair 0 (Nat.pair m (m - 1)) ≤ (2 * N + 2) ^ 4 :=
        pair_nest_le (Nat.zero_le _) hb1
      have hb3 : Nat.pair 0 (m + 1) ≤ (2 * N + 2) ^ 4 := pair_le_quart (Nat.zero_le _) (by omega)
      have hb4 : (2 * N + 1) ^ 2 ≤ (2 * N + 2) ^ 4 := sq_le_quart N
      refine evaln_prec_succ' (k := k' + 1) (by omega) hIH ?_
      refine evaln_comp' (by omega) (evaln_right' (by omega)) ?_
      simp only [Nat.unpair_pair]
      have h4 := evaln_left' (k := k' + 1) (n := Nat.pair m (m - 1)) (by omega)
      simpa using h4

