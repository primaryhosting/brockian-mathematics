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

theorem exc_eq_pentSet {n : ℕ} {S : Finset ℕ} (hn : 0 < n) (hS : S ∈ parts n) (hexc : Exc S) :
    idx S ≠ 0 ∧ pentExp (idx S) = n ∧ pentSet (idx S) = S := by
  have hne := nonempty_of_mem_parts hn hS
  obtain ⟨h0, hsum⟩ := mem_parts.1 hS
  have hsS : lo S ∈ S := lo_mem hne
  have hsM : lo S ≤ hi S := le_hi hsS
  have ht1 : 1 ≤ stair S := stair_pos h0 hne
  have htM : stair S ≤ hi S := stair_le_hi h0
  have hstair : Finset.Icc (hi S - stair S + 1) (hi S) ⊆ S := staircase_subset le_rfl
  have hMt1 : hi S - stair S + 1 ∈ S := hstair (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hsle : lo S ≤ hi S - stair S + 1 := lo_le hMt1
  rcases hexc with ⟨hst, hlt⟩ | ⟨hst, heq⟩
  · have hs1 : 1 ≤ lo S := lo_pos h0 hne
    have hkey : lo S = hi S - stair S + 1 := by omega
    have hM : hi S = 2 * lo S - 1 := by omega
    have hSeq : S = Finset.Ico (lo S) (2 * lo S) := by
      ext x
      simp only [Finset.mem_Ico]
      constructor
      · intro hx
        exact ⟨lo_le hx, by have := le_hi hx; omega⟩
      · intro hx
        exact hstair (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hcard : #S = lo S := by
      conv_lhs => rw [hSeq]
      rw [Nat.card_Ico]; omega
    have hidx : idx S = (lo S : ℤ) := by rw [idx, if_neg (by omega), hcard]
    have hk0 : idx S ≠ 0 := by rw [hidx]; omega
    have hpent : pentSet ((lo S : ℤ)) = Finset.Ico (lo S) (2 * lo S) := by
      rw [pentSet, if_pos (by omega)]; simp
    have hps : pentSet (idx S) = S := by rw [hidx, hpent]; exact hSeq.symm
    obtain ⟨hmem, -, -, -⟩ := pentSet_props hk0
    refine ⟨hk0, ?_, hps⟩
    have h9 := (mem_parts.1 hmem).2
    rw [hps, hsum] at h9
    exact h9.symm
  · have hSeq : S = Finset.Ico (stair S + 1) (2 * stair S + 1) := by
      ext x
      simp only [Finset.mem_Ico]
      constructor
      · intro hx
        have h1 := lo_le hx
        have h2 := le_hi hx
        omega
      · intro hx
        exact hstair (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hcard : #S = stair S := by
      conv_lhs => rw [hSeq]
      rw [Nat.card_Ico]; omega
    have hidx : idx S = -(stair S : ℤ) := by rw [idx, if_pos hst, hcard]
    have hk0 : idx S ≠ 0 := by rw [hidx]; omega
    have hpent : pentSet (-(stair S : ℤ)) = Finset.Ico (stair S + 1) (2 * stair S + 1) := by
      rw [pentSet, if_neg (by omega)]; simp
    have hps : pentSet (idx S) = S := by rw [hidx, hpent]; exact hSeq.symm
    obtain ⟨hmem, -, -, -⟩ := pentSet_props hk0
    refine ⟨hk0, ?_, hps⟩
    have h9 := (mem_parts.1 hmem).2
    rw [hps, hsum] at h9
    exact h9.symm

/-! ### The combinatorial pentagonal number theorem -/

