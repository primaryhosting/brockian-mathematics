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

theorem lowerCount_succ (n : Nat) :
    M.lowerCount (n + 1) = M.lowerCount n + countUpto n (fun i => M.bond i n) := by
  have hlast : countUpto (n + 1) (fun j => M.bond n j && decide (n < j)) = 0 :=
    countUpto_zero fun j hj => by
      simp [Nat.not_lt.mpr (Nat.le_of_lt_succ hj)]
  have hstep : ∀ i, i < n →
      countUpto (n + 1) (fun j => M.bond i j && decide (i < j))
        = countUpto n (fun j => M.bond i j && decide (i < j)) + (if M.bond i n then 1 else 0) := by
    intro i hi
    rw [countUpto_succ]
    simp [hi]
  calc M.lowerCount (n + 1)
      = sumUpto n (fun i => countUpto (n + 1) (fun j => M.bond i j && decide (i < j)))
          + countUpto (n + 1) (fun j => M.bond n j && decide (n < j)) := rfl
    _ = sumUpto n (fun i => countUpto n (fun j => M.bond i j && decide (i < j))
          + (if M.bond i n then 1 else 0)) + 0 := by
          rw [hlast, sumUpto_congr hstep]
    _ = M.lowerCount n + countUpto n (fun i => M.bond i n) := by
          rw [sumUpto_add]; rfl

