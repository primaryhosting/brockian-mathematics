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

theorem countUpto_zero {n : Nat} {p : Nat → Bool} (h : ∀ i, i < n → p i = false) :
    countUpto n p = 0 :=
  sumUpto_zero n fun i hi => by rw [h i hi]; rfl

/-! ## Molecules -/

/-- A molecule: finitely many atoms, labelled `0, 1, ..., atoms - 1`, together with a
symmetric, irreflexive bonding relation. -/
structure Molecule where
  /-- The number of atoms in the molecule. -/
  atoms : Nat
  /-- `bond i j = true` when atoms `i` and `j` are bonded. -/
  bond : Nat → Nat → Bool
  /-- Bonding is symmetric. -/
  bond_symm : ∀ i j, bond i j = bond j i
  /-- No atom is bonded to itself. -/
  bond_irrefl : ∀ i, bond i i = false

namespace Molecule

variable (M : Molecule)

/-- The valence of atom `i`: the number of atoms it is bonded to. -/
