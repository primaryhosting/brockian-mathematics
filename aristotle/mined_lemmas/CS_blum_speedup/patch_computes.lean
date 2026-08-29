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

theorem patch_computes {T : ℕ → ℕ} {c : Code} (hc : Computes c (diagF T)) :
    Computes (patch c (Encodable.encode c)) (diagF T) := by
  intro n
  by_cases hcol : n.unpair.1 = Encodable.encode c
  · have hzero := (diag_col hc hcol).2
    have hen : Encodable.encode c ≤ n := by rw [← hcol]; exact Nat.unpair_left_le n
    have hev : evaln ((2 * n + 2) ^ 4 + 2 * n + 1) (patch c (Encodable.encode c)) n = some 0 :=
      evaln_patch_eq (N := n) hen le_rfl hcol le_rfl
    have hmem : (0 : ℕ) ∈ (patch c (Encodable.encode c)).eval n :=
      evaln_sound (k := (2 * n + 2) ^ 4 + 2 * n + 1) (by simp [hev])
    rw [hzero]
    exact Part.eq_some_iff.2 hmem
  · have hmem : diagF T n ∈ c.eval n := by rw [hc n]; exact Part.mem_some _
    obtain ⟨k₁, hk₁⟩ := evaln_complete.1 hmem
    set N := max (Encodable.encode c) n with hN
    set k := max k₁ ((2 * N + 2) ^ 4 + 2 * N + 2) with hk
    have hck : evaln (k + 1) c n = some (diagF T n) :=
      evaln_mono (le_trans (le_max_left _ _) (Nat.le_succ k)) hk₁
    have hpatch : evaln (k + 1) (patch c (Encodable.encode c)) n = some (diagF T n) :=
      evaln_patch_ne (N := N) (le_max_left _ _) (le_max_right _ _) hcol (le_max_right _ _) hck
    exact Part.eq_some_iff.2 (evaln_sound (k := k + 1) (by simp [hpatch]))

/-- **Blum's speed-up theorem** (infinitely-often form).

For every computable, monotone "speed-up factor" `T` there is a computable
function `f` with the following property: for *every* program `c` computing
`f` there is another program `c'` computing the very same function `f` which,
on infinitely many inputs, beats `c` by more than the factor `T`, i.e.
`T (time c' n) < time c n`.  In particular the problem `f` has no fastest
algorithm. -/
