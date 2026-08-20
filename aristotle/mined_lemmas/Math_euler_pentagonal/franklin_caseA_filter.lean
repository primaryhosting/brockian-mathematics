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

theorem franklin_caseA_filter (h0 : 0 ∉ S) (hne : S.Nonempty) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) :
    ((S.erase (mn S)).filter (fun x => mx S + 1 - mn S ≤ x)).card = mn S := by
  have hm1 : 1 ≤ mn S := Nat.pos_of_ne_zero fun h => h0 (h ▸ mn_mem hne)
  have hmM : mn S ≤ mx S := le_mx (mn_mem hne)
  have : (S.erase (mn S)).filter (fun x => mx S + 1 - mn S ≤ x) =
      S.filter (fun x => mx S + 1 - mn S ≤ x) := by
    ext y
    simp only [mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hy⟩, h⟩; exact ⟨hy, h⟩
    · rintro ⟨hy, h⟩; exact ⟨⟨by omega, hy⟩, h⟩
  rw [this, filter_ge_eq_Icc hA, Nat.card_Icc]
  omega

