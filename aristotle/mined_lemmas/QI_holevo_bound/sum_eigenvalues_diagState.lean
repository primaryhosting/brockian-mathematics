import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma sum_eigenvalues_diagState (r : n → ℝ) (g : ℝ → ℝ)
    (hA : (diagState r).IsHermitian) :
    ∑ i, g (hA.eigenvalues i) = ∑ z, g (r z) := by
  have h1 : (diagState r).charpoly.roots
      = Multiset.map (fun z => ((r z : ℝ) : ℂ)) (Finset.univ : Finset n).val := by
    rw [diagState, Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h2 := hA.roots_charpoly_eq_eigenvalues
  rw [h1] at h2
  have h3 : Multiset.map hA.eigenvalues (Finset.univ : Finset n).val
      = Multiset.map (fun z => (r z : ℝ)) (Finset.univ : Finset n).val := by
    have := congrArg (Multiset.map Complex.re) h2
    simpa [Multiset.map_map, Function.comp_def] using this.symm
  have h4 := congrArg (Multiset.map g) h3
  simp only [Multiset.map_map, Function.comp_def] at h4
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact congrArg Multiset.sum h4

