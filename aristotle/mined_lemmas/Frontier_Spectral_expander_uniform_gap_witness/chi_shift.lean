/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/

lemma chi_shift {k : ℕ} (y x : Cube k) (i : Fin k) :
    chi y (x + bit i) = sgn (y i) * chi y x := by
  have h1 : ∀ j : Fin k, sgn (y j * ((x + bit i) j)) = sgn (y j * x j) * sgn (y j * bit i j) := by
    intro j
    rw [← sgn_add]
    congr 1
    simp [mul_add]
  have h3 : ∏ j : Fin k, sgn (y j * bit i j) = sgn (y i) := by
    have h4 := Finset.prod_eq_single (f := fun j : Fin k => sgn (y j * bit i j))
      (s := Finset.univ) i
      (fun j _ hj => by simp only [bit, Pi.single_eq_of_ne hj, mul_zero, sgn_zero])
      (fun h => absurd (Finset.mem_univ i) h)
    rw [h4]
    simp only [bit, Pi.single_eq_same, mul_one]
  calc chi y (x + bit i) = ∏ j : Fin k, (sgn (y j * x j) * sgn (y j * bit i j)) :=
        Finset.prod_congr rfl (fun j _ => h1 j)
    _ = chi y x * ∏ j : Fin k, sgn (y j * bit i j) := by
        rw [Finset.prod_mul_distrib]; rfl
    _ = sgn (y i) * chi y x := by rw [h3, mul_comm]

