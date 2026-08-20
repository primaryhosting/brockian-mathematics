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

theorem full_spectrum_of_fiber_spectrum [DecidableEq V] [Nonempty V] (hm : 2 ≤ m) (hq : q = 2 * m + 1)
    (hcard : Fintype.card V = q) (hsymm : B.IsSymm)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = (((q : ℝ) - 1) / 2) • (fun _ => 1 : V → ℝ))
    (hr : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 + Real.sqrt q) / 2)) = m)
    (ht : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 - Real.sqrt q) / 2)) = m) :
    (⨆ i, Module.End.eigenspace (lexNormLap B).mulVecLin (lexNLEigenvalues q i)) = ⊤ ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin 0) = 1 ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      ((q : ℝ) * (5 - Real.sqrt 5) / (5 * q - 1))) = 2 ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      ((q : ℝ) * (5 + Real.sqrt 5) / (5 * q - 1))) = 2 ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      ((5 * (q : ℝ) - Real.sqrt q) / (5 * q - 1))) = 5 * m ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      ((5 * (q : ℝ) + Real.sqrt q) / (5 * q - 1))) = 5 * m := by
  obtain ⟨htop, heq⟩ := lexAdj_spectrum hm hq hcard hsymm hreg hr ht
  have key : ∀ i, finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      (lexNLEigenvalues q i)) = lexMultiplicities m i := by
    intro i
    rw [eigenspace_lexNormLap hm hq hcard i, heq i]
    exact lexSpaces_finrank hr ht i
  refine ⟨?_, key 0, key 1, key 2, key 3, key 4⟩
  simp only [eigenspace_lexNormLap hm hq hcard]
  exact htop

end Spectrum

end PentagonLexicographic

/-! # The conditional Paley compiler

`PaleySpectrumData` packages exactly what the compiler needs about the fibre graph `H`:
it is a symmetric `(q-1)/2`-regular graph on `q = 2m+1` vertices whose two nonprincipal
eigenvalues `(-1±√q)/2` have multiplicity `m` each, together with the invariant
decomposition of the function space of `X = C₅[H]`.
-/

namespace PaleyPentagon

open Module Matrix PentagonLexicographic

/-- The input data of the Paley–Pentagon spectral compiler: a *conference graph* `H`
(a symmetric `(q-1)/2`-regular graph on `q = 2m+1 ≥ 5` vertices whose nonprincipal
eigenvalues are `(-1±√q)/2`, each with multiplicity `m = (q-1)/2`), together with the
invariant decomposition of the function space of the lexicographic product `C₅[H]`.

The Paley graphs of prime-power order `q ≡ 1 mod 4` are the motivating family; the
structure is non-vacuous: see `PaleyPentagon.paleyFive`, the Paley graph of order `5`
(which is the pentagon itself). -/
structure PaleySpectrumData where
  /-- The number of vertices of the fibre graph `H`. -/
  q : ℕ
  /-- The common multiplicity `m = (q-1)/2` of the two nonprincipal eigenvalues. -/
  m : ℕ
  hq : q = 2 * m + 1
  hm : 2 ≤ m
  /-- The vertex set of `H`. -/
  V : Type
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  hcard : Fintype.card V = q
  /-- The adjacency matrix of `H`. -/
  B : Matrix V V ℝ
  hsymm : B.IsSymm
  /-- `H` is `(q-1)/2`-regular. -/
  hreg : B *ᵥ (fun _ => 1 : V → ℝ) = (((q : ℝ) - 1) / 2) • (fun _ => 1 : V → ℝ)
  /-- The eigenvalue `(-1+√q)/2` has multiplicity `m`. -/
  hr : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 + Real.sqrt q) / 2)) = m
  /-- The eigenvalue `(-1-√q)/2` has multiplicity `m`. -/
  ht : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 - Real.sqrt q) / 2)) = m
  /-- The invariant decomposition of the function space of `C₅[H]`. -/
  invariant : IsCompl (baseConst V) (baseOrth V) ∧
      (∀ F ∈ baseConst V, lexAdj B *ᵥ F ∈ baseConst V) ∧
      (∀ F ∈ baseOrth V, lexAdj B *ᵥ F ∈ baseOrth V)

attribute [instance] PaleySpectrumData.fintypeV PaleySpectrumData.decEqV

namespace PaleySpectrumData

variable (P : PaleySpectrumData)

