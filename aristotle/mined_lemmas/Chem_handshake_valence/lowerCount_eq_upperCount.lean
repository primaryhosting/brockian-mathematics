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

theorem lowerCount_eq_upperCount (n : Nat) : M.lowerCount n = M.upperCount n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [M.lowerCount_succ, M.upperCount_succ, ih, M.count_to_eq_count_from n n]

end Molecule

/-- **Handshake valence theorem.**  For any molecule, the sum of the valences of its
atoms equals twice the number of its bonds.

This is the chemical form of the graph-theoretic handshake (degree-sum) lemma, which
appears in Mathlib as `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
