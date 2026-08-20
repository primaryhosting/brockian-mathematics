import Mathlib

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
# An effective convergence rate for the twin-prime singular series

The Hardy–Littlewood singular series for prime pairs `(n, n + 2)` is

  `𝔖 = 2 * ∏_{p odd prime} (1 - 1/(p-1)^2)`,

the product being over all odd primes.  In this file we define the partial products
`Brockian.twinPartial N` (product over the odd primes `p ≤ N`), show they converge, and
prove an *effective* rate of convergence:

  `|Brockian.singularSeriesPartial N - Brockian.singularSeries| ≤ 2 / (N - 1)`  for `N ≥ 3`.
-/

namespace Brockian

open Filter Finset
open scoped Topology

/-- The set of odd primes `p ≤ N`, as a `Finset`. -/

theorem twinPartial_sub_le {N M : ℕ} (hN : 3 ≤ N) (hM : N ≤ M) :
    twinPartial N - twinPartial M ≤ 1 / ((N : ℝ) - 1) := by
  classical
  set D := oddPrimesLE M \ oddPrimesLE N with hD
  have hsub : oddPrimesLE N ⊆ oddPrimesLE M := oddPrimesLE_subset hM
  have hsplit : (∏ p ∈ D, twinFactor p) * twinPartial N = twinPartial M :=
    Finset.prod_sdiff hsub
  set Q := ∏ p ∈ D, twinFactor p with hQ
  have hQnn : 0 ≤ Q := Finset.prod_nonneg fun _ hp =>
    twinFactor_nonneg (mem_oddPrimesLE.mp (Finset.mem_sdiff.mp hp).1).2.2
  have hQle : Q ≤ 1 :=
    Finset.prod_le_one (fun _ hp => twinFactor_nonneg (mem_oddPrimesLE.mp (Finset.mem_sdiff.mp hp).1).2.2)
      (fun p _ => twinFactor_le_one p)
  -- Weierstrass bound on `1 - Q`
  have hW : 1 - ∑ p ∈ D, 1 / ((p : ℝ) - 1) ^ 2 ≤ Q := by
    have := one_sub_sum_le_prod_one_sub D (fun p => 1 / ((p : ℝ) - 1) ^ 2)
      (fun p _ => by positivity)
      (fun p hp => by
        have hp3 : 3 ≤ p := (mem_oddPrimesLE.mp (Finset.mem_sdiff.mp hp).1).2.2
        have h3 : (3:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
        rw [div_le_one (by nlinarith)]
        nlinarith)
    simpa [hQ, twinFactor] using this
  -- the sum over `D` is at most the telescoping sum
  have hDsub : D ⊆ Finset.Ioc N M := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hpM, hpN⟩ := hp
    rw [mem_oddPrimesLE] at hpM
    rw [Finset.mem_Ioc]
    refine ⟨?_, hpM.1⟩
    by_contra hcon
    exact hpN (mem_oddPrimesLE.mpr ⟨by omega, hpM.2⟩)
  have hsum : ∑ p ∈ D, 1 / ((p : ℝ) - 1) ^ 2 ≤ ∑ n ∈ Finset.Ioc N M, 1 / ((n : ℝ) - 1) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hDsub (fun i _ _ => by positivity)
  have hM1 : (1:ℝ) ≤ (M : ℝ) - 1 := by
    have : (3:ℕ) ≤ M := le_trans hN hM
    have : (3:ℝ) ≤ (M:ℝ) := by exact_mod_cast this
    linarith
  have htel := sum_inv_sq_Ioc_le (N := N) (by omega) M hM
  have hinv : 0 < 1 / ((M : ℝ) - 1) := by positivity
  have hbound : ∑ p ∈ D, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((N : ℝ) - 1) := by
    linarith
  have hPN := twinPartial_le_one N
  have hPNnn := twinPartial_nonneg N
  have : twinPartial N - twinPartial M = twinPartial N * (1 - Q) := by
    rw [← hsplit]; ring
  rw [this]
  have h1Q : 1 - Q ≤ ∑ p ∈ D, 1 / ((p : ℝ) - 1) ^ 2 := by linarith
  nlinarith [hbound, h1Q]

