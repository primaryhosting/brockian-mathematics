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

theorem evaln_branch_one {A B t : Code} {k' n v w : ℕ} (hn : n ≤ k' + 1)
    (hp1 : Nat.pair n 1 ≤ k' + 1) (hp0 : Nat.pair n 0 ≤ k')
    (hz : Nat.pair n (Nat.pair 0 w) ≤ k' + 1)
    (ht : evaln (k' + 2) t n = some 1) (hA : evaln (k' + 1) A n = some w)
    (hB : evaln (k' + 2) B n = some v) :
    evaln (k' + 2) (branch A B t) n = some v := by
  have hq : evaln (k' + 2) (pair Code.id t) n = some (Nat.pair n 1) :=
    evaln_pair' hn (evaln_id' hn) ht
  have hrec : evaln (k' + 1) (prec A (comp B left)) (Nat.pair n 0) = some w :=
    evaln_prec_zero' hp0 hA
  have hleft : evaln (k' + 2) left (Nat.pair n (Nat.pair 0 w)) = some n := by
    have := evaln_left' (k := k' + 1) (n := Nat.pair n (Nat.pair 0 w)) hz
    simpa using this
  have hg : evaln (k' + 2) (comp B left) (Nat.pair n (Nat.pair 0 w)) = some v :=
    evaln_comp' hz hleft hB
  exact evaln_comp' hn hq (evaln_prec_succ' hp1 hrec hg)

/-! ### The patched program -/

/-- `eqLE e` computes `min (n.unpair.1 - e) 1`; it is `0` exactly when `n.unpair.1 ≤ e`. -/
