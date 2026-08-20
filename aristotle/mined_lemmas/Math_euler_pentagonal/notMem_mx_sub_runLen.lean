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

theorem notMem_mx_sub_runLen {S : Finset ℕ} (h0 : 0 ∉ S) :
    mx S - runLen S ∉ S := by
  rcases eq_or_lt_of_le (runLen_le_mx S) with heq | hlt
  · rw [heq, Nat.sub_self]; exact h0
  · intro hmem
    have key : ¬ (Finset.Icc (mx S + 1 - (runLen S + 1)) (mx S) ⊆ S) :=
      Nat.findGreatest_is_greatest (P := fun t => Finset.Icc (mx S + 1 - t) (mx S) ⊆ S)
        (k := runLen S + 1) (n := mx S) (Nat.lt_succ_self _) (by omega)
    refine key fun x hx => ?_
    simp only [mem_Icc] at hx
    rcases eq_or_lt_of_le hx.1 with heq | hlt'
    · have : x = mx S - runLen S := by omega
      exact this ▸ hmem
    · exact runLen_subset (mem_Icc.mpr ⟨by omega, hx.2⟩)

/-- Characterisation of the run length. -/
