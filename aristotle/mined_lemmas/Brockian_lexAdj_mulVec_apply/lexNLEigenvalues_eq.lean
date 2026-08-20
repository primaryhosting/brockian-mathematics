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

theorem lexNLEigenvalues_eq (hm : 2 ≤ m) (hq : q = 2 * m + 1) (hcard : Fintype.card V = q)
    (i : Fin 5) :
    lexNLEigenvalues q i = 1 - lexAdjEigenvalues q i / lexDegree (V := V) := by
  have hD : lexDegree (V := V) = (5 * (q : ℝ) - 1) / 2 := lexDegree_eq hcard
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq5 : (5 : ℝ) ≤ q := by rw [hq]; push_cast; linarith
  have hDne : (5 * (q : ℝ) - 1) ≠ 0 := by intro h; nlinarith
  fin_cases i
  · show lexNLEigenvalues q 0 = 1 - lexAdjEigenvalues q 0 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_zero, lexAdjEigenvalues_zero, eq_comm, sub_eq_zero, eq_comm,
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring
  · show lexNLEigenvalues q 1 = 1 - lexAdjEigenvalues q 1 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_one, lexAdjEigenvalues_one, phiPlus, eq_sub_iff_add_eq,
      div_add_div _ _ (by intro h; nlinarith) (by intro h; nlinarith),
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring
  · show lexNLEigenvalues q 2 = 1 - lexAdjEigenvalues q 2 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_two, lexAdjEigenvalues_two, phiMinus, eq_sub_iff_add_eq,
      div_add_div _ _ (by intro h; nlinarith) (by intro h; nlinarith),
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring
  · show lexNLEigenvalues q 3 = 1 - lexAdjEigenvalues q 3 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_three, lexAdjEigenvalues_three, eq_sub_iff_add_eq,
      div_add_div _ _ (by intro h; nlinarith) (by intro h; nlinarith),
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring
  · show lexNLEigenvalues q 4 = 1 - lexAdjEigenvalues q 4 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_four, lexAdjEigenvalues_four, eq_sub_iff_add_eq,
      div_add_div _ _ (by intro h; nlinarith) (by intro h; nlinarith),
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring

