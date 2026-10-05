import Mathlib
/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the single `import Mathlib` line, since Lean 4
requires `import` commands to come first in a file.)
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

/-!
## The Weil–Riemann hypothesis, formalized

For a smooth projective variety `X` of dimension `d` over the finite field `F_q`, the Weil
conjectures assert that the zeta function

  `Z_X(T) = exp (∑_{n ≥ 1} N_n T^n / n)`,   `N_n = #X(F_{q^n})`,

is a rational function of the shape `∏_{i=0}^{2d} P_i(T)^{(-1)^{i+1}}` where `P_i ∈ ℤ[T]`,
`P_i(0) = 1`.  Writing `P_i(T) = ∏_j (1 - α_{i,j} T)`, taking the logarithmic derivative of
the displayed identity turns the rationality statement into the point-count formula

  `N_n = ∑_{i=0}^{2d} (-1)^i ∑_j α_{i,j}^n`   for all `n ≥ 1`,

and the *Riemann hypothesis* (proved by Deligne) is the purity statement

  `|α_{i,j}| = q^{i/2}`.

`WeilData` below packages the inverse roots `α_{i,j}` (as a multiset for each cohomological
degree `i`), `WeilData.Computes` is the point-count formula, and `WeilData.RH` is purity.
-/

/-- The inverse roots of the factors `P_i` of the zeta function of a `dim`-dimensional
variety over `F_q`, one multiset for each cohomological degree `i` (empty above degree
`2 * dim`). -/
structure WeilData where
  /-- The cardinality of the base finite field. -/
  q : ℕ
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- The multiset of inverse roots of `P_i`, the `i`-th factor of the zeta function. -/
  roots : ℕ → Multiset ℂ
  /-- There is no cohomology above degree `2 * dim`. -/
  roots_eq_zero : ∀ i : ℕ, 2 * dim < i → roots i = 0

namespace WeilData

/-- The number `∑_{i} (-1)^i ∑_j α_{i,j}^n` predicted by the datum for `#X(F_{q^n})`. -/

lemma timesP1_count (W : WeilData) (n : ℕ) :
    (timesP1 W).count n = (1 + (W.q : ℂ) ^ n) * W.count n := by
  classical
  set K : ℕ := 2 * (W.dim + 1) + 1 with hKdef
  have hK : 2 * W.dim + 1 ≤ K := by omega
  have hbase := W.count_eq_sum_range K hK n
  set f : ℕ → ℂ := fun i => (-1 : ℂ) ^ i * ((W.roots i).map (fun α : ℂ => α ^ n)).sum with hf
  set g : ℕ → ℂ := fun i => (-1 : ℂ) ^ i *
    (((if 2 ≤ i then (W.roots (i - 2)).map (fun α : ℂ => (W.q : ℂ) * α) else 0) : Multiset ℂ).map
      (fun α : ℂ => α ^ n)).sum with hg
  have hsplit : (timesP1 W).count n =
      (∑ i ∈ Finset.range K, f i) + ∑ i ∈ Finset.range K, g i := by
    rw [← Finset.sum_add_distrib]
    simp only [WeilData.count, timesP1, hf, hg, Multiset.map_add, Multiset.sum_add, mul_add]
    rw [show 2 * W.dim + 2 * 1 + 1 = K by omega]
  have hS2 : (∑ i ∈ Finset.range K, g i) = (W.q : ℂ) ^ n * W.count n := by
    have hK' : K = (2 * W.dim + 1) + 1 + 1 := by omega
    rw [hK', Finset.sum_range_succ' g (2 * W.dim + 1 + 1),
      Finset.sum_range_succ' (fun i => g (i + 1)) (2 * W.dim + 1)]
    have hg0 : g 0 = 0 := by simp [hg]
    have hg1 : g 1 = 0 := by simp [hg]
    rw [hg0, hg1, add_zero, add_zero]
    rw [WeilData.count]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    have h2 : (2 : ℕ) ≤ i + 1 + 1 := by omega
    have hsub : i + 1 + 1 - 2 = i := by omega
    have hsign : (-1 : ℂ) ^ (i + 1 + 1) = (-1 : ℂ) ^ i := by ring
    simp only [hg, h2, hsub, hsign, if_true, scaled_power_sum]
    ring
  rw [hsplit, hS2, ← hbase]
  ring

