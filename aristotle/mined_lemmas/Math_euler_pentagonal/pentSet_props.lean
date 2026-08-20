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

theorem pentSet_props {k : ℤ} (hk : k ≠ 0) :
    pentSet k ∈ parts (pentExp k) ∧ Exc (pentSet k) ∧ #(pentSet k) = k.natAbs ∧
      idx (pentSet k) = k := by
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    have hm1 : 1 ≤ m := by omega
    have hset : pentSet (-(m : ℤ)) = Finset.Ico (m + 1) (2 * m + 1) := by
      rw [pentSet, if_neg (by omega)]; simp
    obtain ⟨h0, hlo, hhi, hstair⟩ := Ico_facts (a := m + 1) (b := 2 * m + 1) (by omega) (by omega)
    rw [hset]
    have hcard : #(Finset.Ico (m + 1) (2 * m + 1)) = m := by rw [Nat.card_Ico]; omega
    have hstair' : stair (Finset.Ico (m + 1) (2 * m + 1)) = m := by rw [hstair]; omega
    have hhi' : hi (Finset.Ico (m + 1) (2 * m + 1)) = 2 * m := by rw [hhi]; omega
    have hsum : ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), i = pentExp (-(m : ℤ)) := by
      have h1 := sum_Ico_two_mul' m
      have h2 := pentExp_spec (-(m : ℤ))
      have h4 : 2 * (pentExp (-(m : ℤ)) : ℤ) = 3 * (m : ℤ) ^ 2 + m := by rw [h2]; ring
      have h3 : 2 * pentExp (-(m : ℤ)) = 3 * m ^ 2 + m := by exact_mod_cast h4
      omega
    refine ⟨mem_parts.2 ⟨h0, hsum⟩, ?_, ?_, ?_⟩
    · right; rw [hlo, hstair', hhi']; omega
    · rw [hcard]; omega
    · rw [idx, if_pos (by rw [hlo, hstair']; omega), hcard]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
    have hm1 : 1 ≤ m := by omega
    have hset : pentSet (m : ℤ) = Finset.Ico m (2 * m) := by
      rw [pentSet, if_pos (by omega)]; simp
    obtain ⟨h0, hlo, hhi, hstair⟩ := Ico_facts (a := m) (b := 2 * m) (by omega) (by omega)
    rw [hset]
    have hcard : #(Finset.Ico m (2 * m)) = m := by rw [Nat.card_Ico]; omega
    have hstair' : stair (Finset.Ico m (2 * m)) = m := by rw [hstair]; omega
    have hhi' : hi (Finset.Ico m (2 * m)) = 2 * m - 1 := by rw [hhi]
    have hsum : ∑ i ∈ Finset.Ico m (2 * m), i = pentExp (m : ℤ) := by
      have h1 := sum_Ico_two_mul m
      have h2 := pentExp_spec (m : ℤ)
      have h4 : 2 * (pentExp (m : ℤ) : ℤ) + m = 3 * (m : ℤ) ^ 2 := by rw [h2]; ring
      have h3 : 2 * pentExp (m : ℤ) + m = 3 * m ^ 2 := by exact_mod_cast h4
      omega
    refine ⟨mem_parts.2 ⟨h0, hsum⟩, ?_, ?_, ?_⟩
    · left; rw [hlo, hstair', hhi']; omega
    · rw [hcard]; omega
    · rw [idx, if_neg (by rw [hlo, hstair']; omega), hcard]

