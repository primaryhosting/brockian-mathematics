import Mathlib
import RequestProject.Pentagonal

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

`Math.euler_pentagonal` states the identity of formal power series over `ℤ`
$$\prod_{n = 1}^{\infty} (1 - X^n) = \sum_{k \in \mathbb Z} (-1)^k X^{k(3k-1)/2},$$
where the product and the sum are taken in the `X`-adic (product) topology on `ℤ⟦X⟧`.

`Math.euler_pentagonal_partition` states the corresponding statement for the generating
function of the partition function: the pentagonal series is the multiplicative inverse of
$\sum_{n} p(n) X^n$.

The combinatorial heart of the proof (Franklin's involution) is in
`RequestProject.Pentagonal`.
-/

namespace Math

open PowerSeries Finset Filter
open scoped PowerSeries.WithPiTopology

/-- The pentagonal exponent `k(3k-1)/2`. -/
abbrev pentExp : ℤ → ℕ := Franklin.pentExp

/-- The sign `(-1)^k`. -/
abbrev pentSign : ℤ → ℤ := Franklin.pentSign

/-- The pentagonal series `∑_{k ∈ ℤ} (-1)^k X^{k(3k-1)/2}` as a formal power series over `ℤ`. -/

theorem sum_parts_eq_pentCoeff (n : ℕ) : ∑ S ∈ parts n, (-1 : ℤ) ^ #S = pentCoeff n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [parts_zero, pentCoeff]
    simp [pentExp_zero, pentSign]
  · rw [sum_parts_eq_sum_exc hn, pentCoeff, ← Finset.sum_filter]
    refine Finset.sum_nbij' idx pentSet ?_ ?_ ?_ ?_ ?_
    · intro S hSmem
      rw [Finset.mem_filter] at hSmem
      obtain ⟨hk0, hpe, hps⟩ := exc_eq_pentSet hn hSmem.1 hSmem.2
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hle := natAbs_le_pentExp (idx S)
      rw [hpe] at hle
      exact ⟨⟨by omega, by omega⟩, hpe⟩
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pentExp_zero] at hk
        omega
      obtain ⟨hmem, hexc, -, -⟩ := pentSet_props hk0
      rw [hk.2] at hmem
      exact Finset.mem_filter.2 ⟨hmem, hexc⟩
    · intro S hSmem
      rw [Finset.mem_filter] at hSmem
      exact (exc_eq_pentSet hn hSmem.1 hSmem.2).2.2
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pentExp_zero] at hk
        omega
      exact (pentSet_props hk0).2.2.2
    · intro S hSmem
      rw [Finset.mem_filter] at hSmem
      obtain ⟨hk0, hpe, hps⟩ := exc_eq_pentSet hn hSmem.1 hSmem.2
      rw [pentSign]
      congr 1
      conv_lhs => rw [← hps]
      exact (pentSet_props hk0).2.2.1

end Franklin

