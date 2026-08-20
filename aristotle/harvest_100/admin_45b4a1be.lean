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
def sumUpto : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumUpto n f + f n

/-- `countUpto n p` is the number of `i < n` satisfying the decidable predicate `p`. -/
def countUpto (n : Nat) (p : Nat → Bool) : Nat :=
  sumUpto n (fun i => if p i then 1 else 0)

theorem sumUpto_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    sumUpto n f = sumUpto n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h' : ∀ i, i < n → f i = g i := fun i hi => h i (Nat.lt_succ_of_lt hi)
    simp [sumUpto, ih h', h n (Nat.lt_succ_self n)]

theorem sumUpto_add (n : Nat) (f g : Nat → Nat) :
    sumUpto n (fun i => f i + g i) = sumUpto n f + sumUpto n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumUpto, ih]; omega

theorem sumUpto_const_zero (n : Nat) : sumUpto n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumUpto, ih]

theorem sumUpto_zero (n : Nat) {f : Nat → Nat} (h : ∀ i, i < n → f i = 0) :
    sumUpto n f = 0 := by
  rw [sumUpto_congr (n := n) (f := f) (g := fun _ => 0) h, sumUpto_const_zero]

theorem countUpto_congr {n : Nat} {p q : Nat → Bool} (h : ∀ i, i < n → p i = q i) :
    countUpto n p = countUpto n q :=
  sumUpto_congr fun i hi => by rw [h i hi]

theorem countUpto_succ (n : Nat) (p : Nat → Bool) :
    countUpto (n + 1) p = countUpto n p + (if p n then 1 else 0) := rfl

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
def valence (i : Nat) : Nat := countUpto M.atoms (fun j => M.bond i j)

/-- The number of bonds of the molecule: each bond `{i, j}` is counted once, at its
representative with `i < j`. -/
def bondCount : Nat :=
  sumUpto M.atoms (fun i => countUpto M.atoms (fun j => M.bond i j && decide (i < j)))

/-- The same count, taken over the pairs with `j < i`. -/
def bondCount' : Nat :=
  sumUpto M.atoms (fun i => countUpto M.atoms (fun j => M.bond i j && decide (j < i)))

/-- Splitting the neighbours of an atom into the smaller and the larger ones. -/
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
theorem count_to_eq_count_from (m n : Nat) :
    countUpto n (fun i => M.bond i m) = countUpto n (fun j => M.bond m j) :=
  countUpto_congr fun i _ => M.bond_symm i m

/-- Auxiliary version of `bondCount`/`bondCount'` with the range `n` as an explicit
parameter. -/
def lowerCount (n : Nat) : Nat :=
  sumUpto n (fun i => countUpto n (fun j => M.bond i j && decide (i < j)))

/-- Auxiliary version of `bondCount'` with the range `n` as an explicit parameter. -/
def upperCount (n : Nat) : Nat :=
  sumUpto n (fun i => countUpto n (fun j => M.bond i j && decide (j < i)))

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

theorem upperCount_succ (n : Nat) :
    M.upperCount (n + 1) = M.upperCount n + countUpto n (fun j => M.bond n j) := by
  have hlast : countUpto (n + 1) (fun j => M.bond n j && decide (j < n))
      = countUpto n (fun j => M.bond n j) := by
    rw [countUpto_succ]
    have : countUpto n (fun j => M.bond n j && decide (j < n)) = countUpto n (fun j => M.bond n j) :=
      countUpto_congr fun j hj => by simp [hj]
    simp [this]
  have hstep : ∀ i, i < n →
      countUpto (n + 1) (fun j => M.bond i j && decide (j < i))
        = countUpto n (fun j => M.bond i j && decide (j < i)) := by
    intro i hi
    rw [countUpto_succ]
    simp [Nat.not_lt.mpr (Nat.le_of_lt hi)]
  calc M.upperCount (n + 1)
      = sumUpto n (fun i => countUpto (n + 1) (fun j => M.bond i j && decide (j < i)))
          + countUpto (n + 1) (fun j => M.bond n j && decide (j < n)) := rfl
    _ = M.upperCount n + countUpto n (fun j => M.bond n j) := by
          rw [sumUpto_congr hstep, hlast]; rfl

/-- Each bond is counted once from each of its two ends. -/
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
theorem handshake_valence (M : Molecule) :
    sumUpto M.atoms (fun i => M.valence i) = 2 * M.bondCount := by
  have hsplit : sumUpto M.atoms (fun i => M.valence i)
      = M.lowerCount M.atoms + M.upperCount M.atoms := by
    rw [Molecule.lowerCount, Molecule.upperCount, ← sumUpto_add]
    exact sumUpto_congr fun i _ => M.valence_split i M.atoms
  rw [hsplit, ← M.lowerCount_eq_upperCount]
  have : M.bondCount = M.lowerCount M.atoms := rfl
  omega

/-! ## A sanity check: the water molecule H₂O

Atom `0` is the oxygen, atoms `1` and `2` are the hydrogens; the bonds are `0-1` and
`0-2`. -/

/-- Bonding relation of H₂O on the atoms `0, 1, 2`. -/
def waterBond (i j : Nat) : Bool :=
  decide (i ≠ j) && decide (i + j ≤ 2) && decide (i < 3) && decide (j < 3)

/-- The water molecule. -/
def water : Molecule where
  atoms := 3
  bond := waterBond
  bond_symm := by intro i j; unfold waterBond; simp [Nat.add_comm]; grind
  bond_irrefl := by intro i; unfold waterBond; simp

example : water.valence 0 = 2 := by decide
example : water.valence 1 = 1 := by decide
example : water.valence 2 = 1 := by decide
example : water.bondCount = 2 := by decide
example : sumUpto water.atoms (fun i => water.valence i) = 4 := by decide

end Chem

