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

lemma projectiveSpace_count (q d n : ℕ) :
    (projectiveSpace q d).count n = ∑ j ∈ Finset.range (d + 1), (q : ℂ) ^ (n * j) := by
  induction d with
  | zero => simp [WeilData.count, projectiveSpace]
  | succ d ih =>
      have hrange : 2 * (d + 1) + 1 = (2 * d + 1) + 1 + 1 := by ring
      simp only [WeilData.count, projectiveSpace] at ih ⊢
      rw [hrange, Finset.sum_range_succ, Finset.sum_range_succ]
      have hmain : ∑ i ∈ Finset.range (2 * d + 1), (-1 : ℂ) ^ i *
            (Multiset.map (fun α : ℂ => α ^ n)
              (if 2 ∣ i ∧ i ≤ 2 * (d + 1) then {(q : ℂ) ^ (i / 2)} else 0)).sum
          = ∑ i ∈ Finset.range (2 * d + 1), (-1 : ℂ) ^ i *
            (Multiset.map (fun α : ℂ => α ^ n)
              (if 2 ∣ i ∧ i ≤ 2 * d then {(q : ℂ) ^ (i / 2)} else 0)).sum := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Finset.mem_range] at hi
        have h1 : i ≤ 2 * d := by omega
        have h2 : i ≤ 2 * (d + 1) := by omega
        simp [h1, h2]
      rw [hmain, ih]
      have hodd : ¬ (2 ∣ 2 * d + 1) := by omega
      have heven : 2 ∣ 2 * d + 1 + 1 := by omega
      have hle : 2 * d + 1 + 1 ≤ 2 * (d + 1) := by omega
      have hdiv : (2 * d + 1 + 1) / 2 = d + 1 := by omega
      have hsign : (-1 : ℂ) ^ (2 * d + 1 + 1) = 1 := by
        rw [show 2 * d + 1 + 1 = 2 * (d + 1) by ring, pow_mul]
        simp
      rw [Finset.sum_range_succ (fun j => (q : ℂ) ^ (n * j)) (d + 1)]
      simp only [hodd, heven, hle, hdiv, hsign, false_and, if_false, if_true, and_self,
        Multiset.map_zero, Multiset.sum_zero, mul_zero, add_zero, Multiset.map_singleton,
        Multiset.sum_singleton, one_mul]
      rw [← pow_mul, mul_comm (d + 1) n]

