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

theorem evaln_patch_ne {c : Code} {N e n k v : ℕ} (he : e ≤ N) (hn : n ≤ N)
    (hae : n.unpair.1 ≠ e) (hk : (2 * N + 2) ^ 4 + 2 * N + 2 ≤ k)
    (hc : evaln (k + 1) c n = some v) :
    evaln (k + 1) (patch c e) n = some v := by
  have hq := self_le_quart N
  have hpn0 : Nat.pair n 0 ≤ (2 * N + 2) ^ 4 := pair_le_quart hn (Nat.zero_le _)
  have hpn1 : Nat.pair n 1 ≤ (2 * N + 2) ^ 4 :=
    le_trans (pair_le n 1)
      (le_trans (Nat.pow_le_pow_left (by omega) 2) (Nat.pow_le_pow_right (by omega) (by omega)))
  have hz : Nat.pair n (Nat.pair 0 0) ≤ (2 * N + 2) ^ 4 := by
    have h00 : Nat.pair 0 0 = 0 := by norm_num [Nat.pair]
    rw [h00]; exact hpn0
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rcases lt_or_gt_of_ne hae with hlt | hgt
  · -- `n.unpair.1 < e` : the outer test is `0`, the inner test is `1`
    have hLE : evaln (k' + 1 + 1) (eqLE e) n = some 0 := by
      have := evaln_eqLE (N := N) he hn (k := k' + 1) (by omega)
      have h0 : min (n.unpair.1 - e) 1 = 0 := by omega
      rw [h0] at this; exact this
    have hGE : evaln (k' + 1 + 1) (eqGE e) n = some 1 := by
      have := evaln_eqGE (N := N) he hn (k := k' + 1) (by omega)
      have h0 : min (e - n.unpair.1) 1 = 1 := by omega
      rw [h0] at this; exact this
    have hinner : evaln (k' + 2) (branch zero c (eqGE e)) n = some v :=
      evaln_branch_one (w := 0) (by omega) (by omega) (by omega) (le_trans hz (by omega))
        hGE (evaln_zero' (by omega)) hc
    exact evaln_branch_zero (by omega) (by omega) hLE hinner
  · -- `e < n.unpair.1` : the outer test is `1`
    have hLE : evaln (k' + 1 + 1) (eqLE e) n = some 1 := by
      have := evaln_eqLE (N := N) he hn (k := k' + 1) (by omega)
      have h0 : min (n.unpair.1 - e) 1 = 1 := by omega
      rw [h0] at this; exact this
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    have hGE : evaln (k'' + 1 + 1) (eqGE e) n = some 0 := by
      have := evaln_eqGE (N := N) he hn (k := k'' + 1) (by omega)
      have h0 : min (e - n.unpair.1) 1 = 0 := by omega
      rw [h0] at this; exact this
    have hinner : evaln (k'' + 1 + 1) (branch zero c (eqGE e)) n = some 0 :=
      evaln_branch_zero (by omega) (by omega) hGE (evaln_zero' (by omega))
    exact evaln_branch_one (w := 0) (by omega) (by omega) (by omega) (le_trans hz (by omega))
      hLE hinner hc

/-! ### The diagonal function -/

/-- The step budget used by the diagonalisation. -/
