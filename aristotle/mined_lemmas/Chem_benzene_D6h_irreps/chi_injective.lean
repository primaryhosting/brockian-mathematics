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

theorem chi_injective : Function.Injective chi := by decide

/-- Burnside's sum-of-squares identity for `D₆ₕ`. -/
