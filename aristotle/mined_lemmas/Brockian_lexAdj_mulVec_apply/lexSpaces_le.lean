import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Axiom report

Building this module prints the axiom dependencies of every headline result of the
Paley–Pentagon spectral compiler.  All of them depend only on the three standard axioms of
Lean/Mathlib (`propext`, `Classical.choice`, `Quot.sound`): the development contains no
unproved placeholders, no extra axioms, and no kernel-bypassing evaluation.
-/
import Brockian.PaleyPentagon

-- Target 1: the invariant decomposition.
#print axioms Brockian.PentagonLexicographic.invariant_decomposition

-- Target 2: the full normalized-Laplacian spectrum from the fibre spectrum.
#print axioms Brockian.PentagonLexicographic.full_spectrum_of_fiber_spectrum
#print axioms Brockian.PentagonLexicographic.lexAdj_spectrum

-- Target 3: the conditional compiler from `PaleySpectrumData`, and its non-vacuity.
#print axioms Brockian.PaleyPentagon.full_spectrum
#print axioms Brockian.PaleyPentagon.paleyFive

-- Target 4: the uniform spectral gap.
#print axioms Brockian.PaleyPentagon.uniform_gap

-- Supporting results: the spectrum of the pentagon and the graph-theoretic interpretation.
#print axioms Brockian.cycle5_spectrum
#print axioms Brockian.PentagonLexicographic.adjMatrix_lexProd_cycle5
#print axioms Brockian.PentagonLexicographic.adjMatrix_cycleGraph_five
#print axioms Brockian.PentagonLexicographic.lexAdj_mulVec_one_lexDegree

/-
# The Paley–Pentagon spectral compiler

Let `H` be a regular graph on `q = 2m+1` vertices with adjacency matrix `B`, of degree
`s = (q-1)/2 = m`, whose nonconstant eigenvalues are
`r = (-1+√q)/2` and `τ = (-1-√q)/2`, each of multiplicity `m = (q-1)/2`
(a *conference graph*; the Paley graphs are the standard examples).

Let `X = C₅[H]` be the lexicographic product of the pentagon with `H`, so that
`A_X = A(C₅) ⊗ J_q + I₅ ⊗ B`.  Then `X` is `D`-regular with `D = (5q-1)/2`, and this file
computes the *exact* spectrum of the normalized Laplacian `I - D⁻¹ A_X` of `X`:

| eigenvalue | multiplicity |
| --- | --- |
| `0` | `1` |
| `q(5-√5)/(5q-1)` | `2` |
| `q(5+√5)/(5q-1)` | `2` |
| `(5q-√q)/(5q-1)` | `5(q-1)/2` |
| `(5q+√q)/(5q-1)` | `5(q-1)/2` |

The proof is the "compiler" pattern: the space of functions on `V(X)` splits into
`base ⊗ constants` (where `J_q` acts as `q`, so `A_X` acts as `q·A(C₅) + s`) and
`base ⊗ constant-orthogonal` (where `J_q` acts as `0`, so `A_X` acts as `I₅ ⊗ B`), and the
dimensions of the exhibited eigenspaces already add up to `5q`, which forces them to be the
whole eigenspaces.
-/
import Brockian.Cycle5

namespace Brockian

namespace PentagonLexicographic

open Module Matrix
open scoped Kronecker

variable {V : Type*} [Fintype V]

/-! ## The lexicographic product `C₅[H]` -/

/-- The adjacency matrix `A(C₅) ⊗ J + I ⊗ B` of the lexicographic product `C₅[H]`, where `B`
is the adjacency matrix of `H`. -/

theorem lexSpaces_le (hm : 2 ≤ m) (hq : q = 2 * m + 1) (hcard : Fintype.card V = q)
    (hsymm : B.IsSymm)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = (((q : ℝ) - 1) / 2) • (fun _ => 1 : V → ℝ)) (i : Fin 5) :
    lexSpaces B q i ≤ Module.End.eigenspace (lexAdj B).mulVecLin (lexAdjEigenvalues q i) := by
  have hcardr : (Fintype.card V : ℝ) = q := by rw [hcard]
  have h1 := two_lt_sqrtq hm hq
  have h2 := two_sqrtq_lt hm hq
  fin_cases i
  · exact map_kronConst_le_of_le hreg cyc5Const_le_eigenspace (by rw [hcardr]; simp; ring)
  · exact map_kronConst_le_of_le hreg (cyc5Eig_le_eigenspace phiPlus_sq) (by rw [hcardr]; simp)
  · exact map_kronConst_le_of_le hreg (cyc5Eig_le_eigenspace phiMinus_sq) (by rw [hcardr]; simp)
  · exact fiberPow_eigenspace_le hsymm hreg (by intro h; rw [div_eq_div_iff] at h <;> nlinarith)
  · exact fiberPow_eigenspace_le hsymm hreg (by intro h; rw [div_eq_div_iff] at h <;> nlinarith)

/-! ### The dimension count -/

