/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Classical information quantities -/

section ClassicalDefs

variable {X I Y : Type*}

/-- Shannon entropy `H(P) = -∑ P x * log (P x)` of a finite probability vector. -/

theorem sum_eigenvalues_diagonal (f : ℝ → ℝ) (d : X → ℝ)
    (h : (Matrix.diagonal (fun x => (d x : ℂ))).IsHermitian) :
    ∑ x, f (h.eigenvalues x) = ∑ x, f (d x) := by
  have hcomp : (fun i : X => Polynomial.X - Polynomial.C ((d i : ℝ) : ℂ))
      = (fun a : ℂ => Polynomial.X - Polynomial.C a) ∘ (fun x : X => ((d x : ℝ) : ℂ)) := rfl
  have hroots : (Matrix.diagonal (fun x => (d x : ℂ))).charpoly.roots
      = Multiset.map (fun x => ((d x : ℝ) : ℂ)) Finset.univ.val := by
    rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod, hcomp, ← Multiset.map_map]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  rw [h.roots_charpoly_eq_eigenvalues] at hroots
  have hre := congrArg (Multiset.map Complex.re) hroots
  simp only [Multiset.map_map] at hre
  have hre2 : Multiset.map h.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
    simpa [Function.comp_def] using hre
  have e1 : ∑ x, f (h.eigenvalues x)
      = (Multiset.map f (Multiset.map h.eigenvalues Finset.univ.val)).sum := by
    rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  have e2 : ∑ x, f (d x) = (Multiset.map f (Multiset.map d Finset.univ.val)).sum := by
    rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  rw [e1, e2, hre2]

omit [Fintype X] in
