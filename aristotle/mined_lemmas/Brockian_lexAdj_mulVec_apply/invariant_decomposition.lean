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

theorem invariant_decomposition [Nonempty V] (hsymm : B.IsSymm)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ)) :
    IsCompl (baseConst V) (baseOrth V) ∧
    (∀ F ∈ baseConst V, lexAdj B *ᵥ F ∈ baseConst V) ∧
    (∀ F ∈ baseOrth V, lexAdj B *ᵥ F ∈ baseOrth V) := by
  have hcard : (0:ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- disjointness
    rw [Submodule.disjoint_def]
    rintro F ⟨f, rfl⟩ hF
    rw [baseOrth, mem_fiberPow] at hF
    have : ∀ i, f i = 0 := by
      intro i
      have := hF i
      rw [mem_sumZero] at this
      simp only [kronConst_apply] at this
      rw [Finset.sum_const, nsmul_eq_mul] at this
      have hne : ((Finset.univ : Finset V).card : ℝ) ≠ 0 := by
        rw [Finset.card_univ]; exact_mod_cast Fintype.card_ne_zero
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hne
      · exact h
    ext p
    simp [this]
  · -- codisjointness
    rw [codisjoint_iff, eq_top_iff]
    intro F _
    set c : Fin 5 → ℝ := fun i => (∑ v, F (i, v)) / Fintype.card V with hc
    refine Submodule.mem_sup.2 ⟨kronConst V c, ⟨c, rfl⟩, F - kronConst V c, ?_, ?_⟩
    · rw [baseOrth, mem_fiberPow]
      intro i
      rw [mem_sumZero]
      simp only [Pi.sub_apply, kronConst_apply, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, hc, Finset.card_univ]
      field_simp
      ring
    · abel
  · -- invariance of the constant part
    rintro F ⟨f, rfl⟩
    exact ⟨_, (lexAdj_mulVec_kronConst hreg f).symm⟩
  · -- invariance of the orthogonal part
    intro F hF
    rw [baseOrth, mem_fiberPow] at hF ⊢
    intro i
    rw [mem_sumZero]
    have hz : ∀ j, ∑ w, F (j, w) = 0 := fun j => (mem_sumZero.1 (hF j))
    have : ∑ v, (lexAdj B *ᵥ F) (i, v)
        = ∑ v, ((∑ j, cycle5 i j * ∑ w, F (j, w)) + (B *ᵥ fun w => F (i, w)) v) :=
      Finset.sum_congr rfl fun v _ => lexAdj_mulVec_apply B F i v
    rw [this, Finset.sum_add_distrib, sum_mulVec_of_regular hsymm hreg]
    simp [hz]

end Regular

/-! ## The five eigenspaces of `X = C₅[H]` -/

section Spectrum

variable {B : Matrix V V ℝ} {m q : ℕ}

/-- The five eigenvalues of the adjacency matrix of `X = C₅[H]`, where `H` is a conference
graph on `q` vertices: `2q + s`, `qφ₊ + s`, `qφ₋ + s` (from the constant fibres) and
`(-1±√q)/2` (from the fibrewise eigenvectors), with `s = (q-1)/2`. -/
