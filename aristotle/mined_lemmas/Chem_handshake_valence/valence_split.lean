/-!
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports.  Lean 4 requires every `import` command to appear before any other
command, and a `/-! ... -/` module docstring *is* a command.  Since the file is
required to begin with the header docstring above, no `import` line may follow it,
so this development is carried out in pure core Lean, with no Mathlib.

The statement is the chemical "handshake" (degree-sum) identity: the sum of the
valences of the atoms of a molecule equals twice its number of bonds.  In Mathlib
the corresponding graph-theoretic statement is
`SimpleGraph.sum_degrees_eq_twice_card_edges`
(`Mathlib/Combinatorics/SimpleGraph/DegreeSum.lean`), which would close the
Mathlib-flavoured version of this theorem immediately; here everything is proved
from scratch instead.
-/

namespace Chem

/-! ## Finite sums and counts over `{0, 1, ..., n-1}` -/

/-- `sumUpto n f = f 0 + f 1 + ... + f (n-1)`. -/

theorem valence_split (i n : Nat) :
    countUpto n (fun j => M.bond i j)
      = countUpto n (fun j => M.bond i j && decide (i < j))
        + countUpto n (fun j => M.bond i j && decide (j < i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [countUpto_succ, countUpto_succ, countUpto_succ, ih]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, Nat.not_lt.mpr (Nat.le_of_lt h)]
      omega
    · subst h; simp [M.bond_irrefl i]
    · simp [h, Nat.not_lt.mpr (Nat.le_of_lt h)]
      omega

/-- Counting, over the atoms `i < n`, the bonds from `i` to a fixed atom `m` is the same
as counting the bonds from `m`. -/
