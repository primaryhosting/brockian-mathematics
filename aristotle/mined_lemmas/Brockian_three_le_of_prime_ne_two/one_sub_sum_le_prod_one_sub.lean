/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The singular series considered here is the Hardy–Littlewood twin-prime singular series
(without the leading factor `2`),
`𝔖 = ∏_{p odd prime} (1 - 1/(p-1)^2)`,
realised as the limit of its truncations `𝔖(N) = ∏_{p < N, p odd prime} (1 - 1/(p-1)^2)`.

The main result `Brockian.SingularSeriesConvergenceRate` is an *effective* convergence rate:
for every `N ≥ 3`,
`|𝔖(N) - 𝔖| ≤ 1/(N-2)`.
-/

namespace Brockian

open Finset

/-- The local factor at `p`: `1 - 1/(p-1)^2` at odd primes, and `1` at all other naturals. -/

lemma one_sub_sum_le_prod_one_sub {s : Finset ℕ} {a : ℕ → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      have hx0 : 0 ≤ a x := h0 x (Finset.mem_insert_self x s)
      have hx1 : a x ≤ 1 := h1 x (Finset.mem_insert_self x s)
      have h0' : ∀ i ∈ s, 0 ≤ a i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1' : ∀ i ∈ s, a i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have ihs := ih h0' h1'
      have hsum : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg h0'
      rw [Finset.prod_insert hx, Finset.sum_insert hx]
      nlinarith [ihs, hsum, hx0, hx1]

/-! ### Basic properties of the truncations -/

