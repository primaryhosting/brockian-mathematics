import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

namespace Frontier

/-! ## A finite-sum Gibbs inequality

The nonnegativity of a Kullback–Leibler divergence between two finitely supported
probability distributions. -/

/-- One term of Gibbs' inequality: `p - q ≤ p * log (p / q)`, under the absolute
continuity assumption `q = 0 → p = 0`. -/

theorem gibbs_sum_nonneg {ι : Type} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0)
    (hsp : ∑ i, p i = 1) (hsq : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have h := Finset.sum_le_sum (f := fun i => p i - q i)
      (g := fun i => p i * Real.log (p i / q i))
      (s := Finset.univ) (fun i _ => gibbs_term (hp i) (hq i) (hac i))
  simpa [Finset.sum_sub_distrib, hsp, hsq] using h

/-! ## Systems, bipartitions and effective information -/

variable {V S : Type} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]

/-- A finite discrete dynamical system: `V` is the set of elements, each carrying a
state in `S`, and `tpm` is the transition probability matrix on global states. -/
structure System (V S : Type) [Fintype V] [DecidableEq V] [Fintype S] where
  /-- transition probability from a global state to a global state -/
  tpm : (V → S) → (V → S) → ℝ
  tpm_nonneg : ∀ x y, 0 ≤ tpm x y
  tpm_sum : ∀ x, ∑ y, tpm x y = 1

/-- The part of a global state living on `A`. -/
