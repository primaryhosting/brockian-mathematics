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

theorem franklin_caseA_mn_gt (hS : S ∈ DPart n) (hn : 1 ≤ n) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) : runLen (franklin S) < mn (franklin S) := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have hTne : (franklin S).Nonempty :=
    ⟨mx S + 1, (mem_franklin_caseA h0 hne hA hM _).mpr (Or.inr ⟨by omega, le_rfl⟩)⟩
  rw [franklin_caseA_runLen hS hn hA hM]
  rcases (mem_franklin_caseA h0 hne hA hM _).mp (mn_mem hTne) with ⟨hx1, hx2, -⟩ | ⟨h, -⟩
  · have := mn_le hx1; omega
  · omega

