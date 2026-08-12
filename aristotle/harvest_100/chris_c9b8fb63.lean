import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

/-! # The character table of the point group `D₆ₕ` (benzene)

`D₆ₕ`, the point group of the benzene molecule, is the direct product of the dihedral group
`D₆` (order 12) with the inversion group `Cᵢ ≅ C₂`, hence has order 24.  We model it as
`DihedralGroup 6 × Multiplicative (ZMod 2)`.

We record the standard character table (12 irreducible representations
`A₁g, A₂g, B₁g, B₂g, E₁g, E₂g, A₁u, A₂u, B₁u, B₂u, E₁u, E₂u`
against the 12 classes `E, 2C₆, 2C₃, C₂, 3C₂', 3C₂'', i, 2S₃, 2S₆, σ_h, 3σ_d, 3σ_v`) and prove:

* the group really has 12 conjugacy classes, represented by the 12 listed symmetry classes,
  with the listed class sizes;
* the 12 rows of the table are orthonormal for the class-size weighted inner product
  (in particular they are pairwise distinct), and the columns are orthogonal;
* the dimensions satisfy Burnside's sum-of-squares identity `∑ dᵢ² = |D₆ₕ| = 24`.

Together these say that the character table of `D₆ₕ` has the correct number of irreducible
representations, namely one for each conjugacy class.
-/

/-- The point group `D₆ₕ`, realized as `D₆ × Cᵢ`. -/
abbrev D6h := DihedralGroup 6 × Multiplicative (ZMod 2)

/-- Labels of the 12 irreducible representations of `D₆ₕ`. -/
inductive Irrep
  | A1g | A2g | B1g | B2g | E1g | E2g
  | A1u | A2u | B1u | B2u | E1u | E2u
  deriving DecidableEq, Fintype, Repr

/-- Labels of the 12 conjugacy classes (symmetry-operation classes) of `D₆ₕ`. -/
inductive Cls
  | E | C6 | C3 | C2 | C2' | C2'' | inv | S3 | S6 | sigmah | sigmad | sigmav
  deriving DecidableEq, Fintype, Repr

/-- A representative group element for each symmetry class. -/
def rep : Cls → D6h
  | .E      => (DihedralGroup.r 0, 1)
  | .C6     => (DihedralGroup.r 1, 1)
  | .C3     => (DihedralGroup.r 2, 1)
  | .C2     => (DihedralGroup.r 3, 1)
  | .C2'    => (DihedralGroup.sr 0, 1)
  | .C2''   => (DihedralGroup.sr 1, 1)
  | .inv    => (DihedralGroup.r 0, Multiplicative.ofAdd 1)
  | .S3     => (DihedralGroup.r 1, Multiplicative.ofAdd 1)
  | .S6     => (DihedralGroup.r 2, Multiplicative.ofAdd 1)
  | .sigmah => (DihedralGroup.r 3, Multiplicative.ofAdd 1)
  | .sigmad => (DihedralGroup.sr 0, Multiplicative.ofAdd 1)
  | .sigmav => (DihedralGroup.sr 1, Multiplicative.ofAdd 1)

/-- The number of elements in each symmetry class. -/
def classSize : Cls → ℤ
  | .E => 1 | .C6 => 2 | .C3 => 2 | .C2 => 1 | .C2' => 3 | .C2'' => 3
  | .inv => 1 | .S3 => 2 | .S6 => 2 | .sigmah => 1 | .sigmad => 3 | .sigmav => 3

/-- The character table of `D₆ₕ`: `chi X c` is the character of the irreducible
representation `X` on the class `c`. -/
def chi : Irrep → Cls → ℤ
  --        E   C6  C3  C2  C2' C2''  i   S3  S6  σh  σd  σv
  | .A1g => fun c => match c with
    | .E => 1 | .C6 => 1 | .C3 => 1 | .C2 => 1 | .C2' => 1 | .C2'' => 1
    | .inv => 1 | .S3 => 1 | .S6 => 1 | .sigmah => 1 | .sigmad => 1 | .sigmav => 1
  | .A2g => fun c => match c with
    | .E => 1 | .C6 => 1 | .C3 => 1 | .C2 => 1 | .C2' => -1 | .C2'' => -1
    | .inv => 1 | .S3 => 1 | .S6 => 1 | .sigmah => 1 | .sigmad => -1 | .sigmav => -1
  | .B1g => fun c => match c with
    | .E => 1 | .C6 => -1 | .C3 => 1 | .C2 => -1 | .C2' => 1 | .C2'' => -1
    | .inv => 1 | .S3 => -1 | .S6 => 1 | .sigmah => -1 | .sigmad => 1 | .sigmav => -1
  | .B2g => fun c => match c with
    | .E => 1 | .C6 => -1 | .C3 => 1 | .C2 => -1 | .C2' => -1 | .C2'' => 1
    | .inv => 1 | .S3 => -1 | .S6 => 1 | .sigmah => -1 | .sigmad => -1 | .sigmav => 1
  | .E1g => fun c => match c with
    | .E => 2 | .C6 => 1 | .C3 => -1 | .C2 => -2 | .C2' => 0 | .C2'' => 0
    | .inv => 2 | .S3 => 1 | .S6 => -1 | .sigmah => -2 | .sigmad => 0 | .sigmav => 0
  | .E2g => fun c => match c with
    | .E => 2 | .C6 => -1 | .C3 => -1 | .C2 => 2 | .C2' => 0 | .C2'' => 0
    | .inv => 2 | .S3 => -1 | .S6 => -1 | .sigmah => 2 | .sigmad => 0 | .sigmav => 0
  | .A1u => fun c => match c with
    | .E => 1 | .C6 => 1 | .C3 => 1 | .C2 => 1 | .C2' => 1 | .C2'' => 1
    | .inv => -1 | .S3 => -1 | .S6 => -1 | .sigmah => -1 | .sigmad => -1 | .sigmav => -1
  | .A2u => fun c => match c with
    | .E => 1 | .C6 => 1 | .C3 => 1 | .C2 => 1 | .C2' => -1 | .C2'' => -1
    | .inv => -1 | .S3 => -1 | .S6 => -1 | .sigmah => -1 | .sigmad => 1 | .sigmav => 1
  | .B1u => fun c => match c with
    | .E => 1 | .C6 => -1 | .C3 => 1 | .C2 => -1 | .C2' => 1 | .C2'' => -1
    | .inv => -1 | .S3 => 1 | .S6 => -1 | .sigmah => 1 | .sigmad => -1 | .sigmav => 1
  | .B2u => fun c => match c with
    | .E => 1 | .C6 => -1 | .C3 => 1 | .C2 => -1 | .C2' => -1 | .C2'' => 1
    | .inv => -1 | .S3 => 1 | .S6 => -1 | .sigmah => 1 | .sigmad => 1 | .sigmav => -1
  | .E1u => fun c => match c with
    | .E => 2 | .C6 => 1 | .C3 => -1 | .C2 => -2 | .C2' => 0 | .C2'' => 0
    | .inv => -2 | .S3 => -1 | .S6 => 1 | .sigmah => 2 | .sigmad => 0 | .sigmav => 0
  | .E2u => fun c => match c with
    | .E => 2 | .C6 => -1 | .C3 => -1 | .C2 => 2 | .C2' => 0 | .C2'' => 0
    | .inv => -2 | .S3 => 1 | .S6 => 1 | .sigmah => -2 | .sigmad => 0 | .sigmav => 0

/-- The dimension of an irreducible representation is its character on the identity class. -/
def dim (X : Irrep) : ℤ := chi X .E

/-- The order of `D₆ₕ` is 24. -/
theorem card_D6h : Fintype.card D6h = 24 := by decide

/-- `D₆ₕ` has exactly 12 conjugacy classes. -/
theorem card_conjClasses_D6h : Fintype.card (ConjClasses D6h) = 12 := by decide

/-- The 12 listed symmetry classes are pairwise non-conjugate and exhaust all conjugacy
classes of `D₆ₕ`. -/
theorem rep_bijective : Function.Bijective (fun c : Cls => ConjClasses.mk (rep c)) := by decide

/-- The listed class sizes are the true sizes of the conjugacy classes of `D₆ₕ`. -/
theorem classSize_eq (c : Cls) :
    ((Finset.univ.filter fun g : D6h => ConjClasses.mk g = ConjClasses.mk (rep c)).card : ℤ)
      = classSize c := by
  revert c; decide

/-- The class sizes add up to the order of the group. -/
theorem sum_classSize : ∑ c : Cls, classSize c = 24 := by decide

/-- Row orthonormality of the character table: the rows are orthonormal for the
class-size weighted inner product `⟪χ, ψ⟫ = (1/|G|) ∑_c |c| χ(c) ψ(c)`. -/
theorem row_orthogonality (X Y : Irrep) :
    ∑ c : Cls, classSize c * chi X c * chi Y c = if X = Y then 24 else 0 := by
  revert X Y; decide

/-- Column orthogonality of the character table. -/
theorem col_orthogonality (c d : Cls) :
    ∑ X : Irrep, chi X c * chi X d = if c = d then 24 / classSize c else 0 := by
  revert c d; decide

/-- Distinct irreducible representations have distinct characters. -/
theorem chi_injective : Function.Injective chi := by decide

/-- Burnside's sum-of-squares identity for `D₆ₕ`. -/
theorem sum_sq_dim : ∑ X : Irrep, (dim X) ^ 2 = 24 := by decide

/-- **The character table of `D₆ₕ` has the correct number of irreducible representations.**

Concretely, for the benzene point group `D₆ₕ = D₆ × Cᵢ` (of order 24):

1. the number of rows of the character table equals the number of conjugacy classes of the
   group, both being 12, and the 12 tabulated symmetry classes `E, 2C₆, 2C₃, C₂, 3C₂', 3C₂'',
   i, 2S₃, 2S₆, σ_h, 3σ_d, 3σ_v` biject with the conjugacy classes, with the tabulated sizes;
2. the rows are orthonormal (so the 12 characters are pairwise distinct), and the columns are
   orthogonal;
3. the dimensions satisfy `∑ dᵢ² = |D₆ₕ| = 24`, so no irreducible representation is missing. -/
theorem benzene_D6h_irreps :
    Fintype.card Irrep = Fintype.card (ConjClasses D6h) ∧
    Fintype.card Irrep = 12 ∧
    Function.Bijective (fun c : Cls => ConjClasses.mk (rep c)) ∧
    (∀ c : Cls,
      ((Finset.univ.filter fun g : D6h => ConjClasses.mk g = ConjClasses.mk (rep c)).card : ℤ)
        = classSize c) ∧
    (∀ X Y : Irrep, ∑ c : Cls, classSize c * chi X c * chi Y c = if X = Y then 24 else 0) ∧
    Function.Injective chi ∧
    ∑ X : Irrep, (dim X) ^ 2 = Fintype.card D6h := by
  refine ⟨?_, ?_, rep_bijective, classSize_eq, row_orthogonality, chi_injective, ?_⟩
  · rw [card_conjClasses_D6h]; decide
  · decide
  · rw [card_D6h]; exact sum_sq_dim

end Chem

