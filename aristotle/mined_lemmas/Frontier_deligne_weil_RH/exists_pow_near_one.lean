/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

open Filter Metric

/-!
## The zeta datum of a variety over a finite field

Mathlib has no étale cohomology, so we formalize the *shape* of the Weil conjectures at
the level of the numerical data they concern: for a `d`-dimensional variety `X` over `𝔽_q`
one has Betti numbers `b i`, inverse roots `α i j` of the characteristic polynomials
`P i` of Frobenius on the `i`-th cohomology group, and point counts
`N n = #X(𝔽_{q^n})` linked by the Grothendieck–Lefschetz trace formula.

The Riemann hypothesis part of the Weil conjectures (Deligne, 1974) is the assertion that
every inverse root occurring in degree `i` has archimedean absolute value `q ^ (i / 2)`.
-/

/-- Numerical zeta-function data attached to a `dim`-dimensional variety over `𝔽_q`:
Betti numbers, the inverse roots of Frobenius in each cohomological degree, the point
counts over the extensions `𝔽_{q ^ n}`, and the Lefschetz trace formula relating them. -/
structure WeilDatum where
  /-- the cardinality of the base field -/
  q : ℕ
  /-- the base field is a genuine finite field -/
  hq : 1 < q
  /-- the dimension of the variety -/
  dim : ℕ
  /-- the Betti numbers -/
  betti : ℕ → ℕ
  /-- the inverse roots of Frobenius acting on the `i`-th cohomology group -/
  root : (i : ℕ) → Fin (betti i) → ℂ
  /-- `pointCount n` is the number of `𝔽_{q ^ n}`-points -/
  pointCount : ℕ → ℕ
  /-- cohomology vanishes above degree `2 * dim` -/
  betti_vanishing : ∀ i, 2 * dim < i → betti i = 0
  /-- the Grothendieck–Lefschetz trace formula -/
  lefschetz : ∀ n : ℕ, 1 ≤ n →
    (pointCount n : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1), (-1 : ℂ) ^ i * ∑ j, (root i j) ^ n

/-- The Riemann hypothesis for a zeta datum: every inverse root of Frobenius in
cohomological degree `i` has absolute value `q ^ (i / 2)` (Deligne's theorem, for the
data coming from a smooth projective variety). -/

theorem exists_pow_near_one {m : ℕ} (β : Fin m → ℂ) (hβ : ∀ j, ‖β j‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ ∀ j, ‖β j ^ n - 1‖ < ε := by
  classical
  set x : ℕ → (Fin m → ℂ) := fun k j => β j ^ (k * (N + 1)) with hx
  have hS : IsCompact (Set.univ.pi (fun _ : Fin m => Metric.closedBall (0 : ℂ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall 0 1)
  have hmem : ∀ k, x k ∈ Set.univ.pi (fun _ : Fin m => Metric.closedBall (0 : ℂ) 1) := by
    intro k j _
    simp [hx, mem_closedBall, dist_eq_norm, norm_pow, hβ j]
  obtain ⟨a, -, psi, hpsi, hlim⟩ := hS.tendsto_subseq hmem
  have hc := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  obtain ⟨K, hK⟩ := hc ε hε
  have hlt : psi K < psi (K + 1) := hpsi (Nat.lt_succ_self K)
  have hd : dist (x (psi (K + 1))) (x (psi K)) < ε := hK (K + 1) (by omega) K (by omega)
  have hsum : psi K + (psi (K + 1) - psi K) = psi (K + 1) := by omega
  refine ⟨(psi (K + 1) - psi K) * (N + 1), ?_, ?_, ?_⟩
  · calc N ≤ 1 * (N + 1) := by omega
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  · intro j
    have hj := lt_of_le_of_lt (dist_le_pi_dist (x (psi (K + 1))) (x (psi K)) j) hd
    rw [dist_eq_norm] at hj
    have hfac : β j ^ (psi (K + 1) * (N + 1)) - β j ^ (psi K * (N + 1))
        = β j ^ (psi K * (N + 1)) * (β j ^ ((psi (K + 1) - psi K) * (N + 1)) - 1) := by
      rw [mul_sub, mul_one, ← pow_add, ← Nat.add_mul, hsum]
    simp only [hx] at hj
    rw [hfac, norm_mul, norm_pow, hβ j, one_pow, one_mul] at hj
    exact hj

