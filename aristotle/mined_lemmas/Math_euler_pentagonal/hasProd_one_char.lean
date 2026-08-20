import Mathlib
import RequestProject.Pentagonal.GenFun

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

/-!
# Euler's pentagonal number theorem

`Math.euler_pentagonal` states that the generating function of the partition numbers
`p(n) = Fintype.card n.Partition` is the inverse of the pentagonal series
`∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`, as formal power series over `ℤ`.

`Math.euler_pentagonal_prod` is the classical product form
`∏_{i ≥ 1} (1 - q^i) = ∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`.
-/

open scoped PowerSeries.WithPiTopology

namespace Math

/-- **Euler's pentagonal number theorem** for the partition generating function:
`(∑_{n ≥ 0} p(n) q^n) * (∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}) = 1` in `ℤ⟦X⟧`.
Here the inner sum over `k ∈ Finset.Icc (-n) n` picks out the (at most one) integer `k`
with `n = k(3k-1)/2`, contributing `(-1)^k`. -/

theorem hasProd_one_char :
    HasProd (fun i => ∑' j : ℕ, ((X : ℤ⟦X⟧) ^ (i + 1)) ^ j)
      (Nat.Partition.genFun (fun _ _ => (1 : ℤ))) := by
  have h := Nat.Partition.hasProd_genFun (fun _ _ => (1 : ℤ))
  convert h using 2 with i
  have hc : ((X : ℤ⟦X⟧) ^ (i + 1)).constantCoeff = 0 := by
    simp
  have hsummable : Summable (fun j : ℕ => ((X : ℤ⟦X⟧) ^ (i + 1)) ^ j) :=
    WithPiTopology.summable_pow_of_constantCoeff_eq_zero hc
  rw [hsummable.tsum_eq_zero_add]
  simp only [pow_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [← pow_mul, one_smul]

