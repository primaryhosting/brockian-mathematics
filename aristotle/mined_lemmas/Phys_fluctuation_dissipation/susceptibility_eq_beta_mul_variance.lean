import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

namespace Phys

open Set MeasureTheory Filter Topology

/-!
## The classical fluctuation–dissipation relation

Let `C t = ⟨A(0) A(t)⟩` be the equilibrium autocorrelation function of an observable `A`
in a system at inverse temperature `β`.  The (classical, Kubo) fluctuation–dissipation

theorem susceptibility_eq_beta_mul_variance (β : ℝ) (E A : ι → ℝ) (f : ℝ) :
    HasDerivAt (fun f => gibbsAvg β E A f A)
      (β * (gibbsAvg β E A f (fun i => A i ^ 2) - (gibbsAvg β E A f A) ^ 2)) f := by
  have hZ : HasDerivAt (gibbsPartition β E A) (∑ i, β * A i * gibbsWeight β E A f i) f := by
    have h := HasDerivAt.fun_sum
      (fun (i : ι) (_ : i ∈ (Finset.univ : Finset ι)) => hasDerivAt_gibbsWeight β E A f i)
    simpa [gibbsPartition] using h
  have hN : HasDerivAt (fun f => ∑ i, A i * gibbsWeight β E A f i)
      (∑ i, A i * (β * A i * gibbsWeight β E A f i)) f :=
    HasDerivAt.fun_sum (fun i _ => (hasDerivAt_gibbsWeight β E A f i).const_mul (A i))
  have hZne : gibbsPartition β E A f ≠ 0 := (gibbsPartition_pos β E A f).ne'
  refine (hN.div hZ hZne).congr_deriv ?_
  have e1 : ∑ i, A i * (β * A i * gibbsWeight β E A f i)
      = β * ∑ i, A i ^ 2 * gibbsWeight β E A f i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, β * A i * gibbsWeight β E A f i = β * ∑ i, A i * gibbsWeight β E A f i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  simp only [gibbsAvg, e1, e2]
  field_simp

/-- The static fluctuation–dissipation relation in `deriv` form: the zero-field static
susceptibility is `β` times the equilibrium variance of `A`. -/
