/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker's invariance principle

This file proves Donsker's invariance principle at the level of finite dimensional
distributions, for a random walk with independent standard Gaussian steps.

If `(X i)` are independent standard Gaussian random variables, `S n = X 0 + ⋯ + X (n-1)` and
`W n t = S ⌊n t⌋ / √n` is the diffusively rescaled walk, then for every nondecreasing sequence
of nonnegative times `t 0 ≤ t 1 ≤ ⋯` and every bounded continuous `f : ℝ^k → ℝ`,
`E[f (W n (t 0), …, W n (t (k-1)))]` converges to `E[f (B (t 0), …, B (t (k-1)))]`, where `B` is
any Brownian motion; that is, the finite dimensional distributions of the rescaled walk converge
weakly to those of Brownian motion.

## Main results

* `Math2.donsker_invariance`: the statement above, with the limit expressed through an
  arbitrary process `B` satisfying `Math2.IsBrownianMotion`.
* `Math2.donsker_invariance_law`: the same convergence with the limit written explicitly as the
  finite dimensional Wiener law `Math2.wienerFdd k t`, a statement which involves no Brownian
  motion at all.
* `Math2.covStep_wienerFdd`: the limit law is the centered Gaussian law on `ℝ^k` with covariance
  `min (t i) (t j)`, i.e. the covariance of Brownian motion.
* `Math2.map_brownian_eq_wienerFdd`: any Brownian motion sampled at the times `t` has law
  `wienerFdd k t`.
* `Math2.exists_gaussian_steps`: the assumptions on the steps of the walk are satisfiable.

## Implementation notes

Weak convergence is expressed, as usual, by convergence of the integrals of bounded continuous
test functions.  The law of each finite dimensional vector is identified through its
characteristic function (`Math2.charFun_map_linear`), and the convergence then follows from
dominated convergence, since all the laws involved are images of a fixed standard Gaussian
measure under linear maps depending continuously on the (rescaled) times.

The steps of the walk are assumed to be standard Gaussian.  Brownian motion is axiomatised
through its finite dimensional distributions (`Math2.IsBrownianMotion`); no path regularity is
required, and no construction of Brownian motion is carried out here — this is why the
Brownian-motion-free version `Math2.donsker_invariance_law` is also proved.
-/

open MeasureTheory ProbabilityTheory Filter Topology WithLp
open scoped NNReal

namespace Math2

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `IsBrownianMotion B P` says that the real valued process `(B t)_{t ≥ 0}` is a Brownian
motion under the probability measure `P`: it starts at `0`, it has independent increments, and
the increment over `[s, r]` is centered Gaussian with variance `r - s`.

Only the finite dimensional distributions are described here (no path regularity is required);
this is exactly what is needed for the convergence of finite dimensional distributions in
Donsker's theorem. -/
structure IsBrownianMotion (B : ℝ → Ω → ℝ) (P : Measure Ω) : Prop where
  /-- Each `B s` is measurable. -/
  measurable : ∀ s, Measurable (B s)
  /-- The process starts at `0`. -/
  start_zero : ∀ᵐ ω ∂P, B 0 ω = 0
  /-- The increment over `[s, r]` is centered Gaussian with variance `r - s`. -/
  gaussian_increment : ∀ s r : ℝ, 0 ≤ s → s ≤ r →
    P.map (fun ω ↦ B r ω - B s ω) = gaussianReal 0 (Real.toNNReal (r - s))
  /-- The increments along any nondecreasing sequence of times are independent. -/
  indep_increments : ∀ (m : ℕ) (v : ℕ → ℝ), Monotone v → 0 ≤ v 0 →
    iIndepFun (fun (i : Fin m) ω ↦ B (v ((i : ℕ) + 1)) ω - B (v (i : ℕ)) ω) P

/-! ### Gaussian vectors with independent increments -/

/-- `stepMap σ z j = ∑_{i ≤ j} σ i * z i`: the partial sums of the rescaled coordinates. -/

lemma map_walk_eq_gaussVec {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {k : ℕ} (u : ℕ → ℝ) (hu0 : u 0 = 0) (humono : Monotone u) {n : ℕ} (hn : 1 ≤ n) :
    (P.map fun ω ↦ (toLp 2 (fun j : Fin k ↦
        (∑ i ∈ Finset.range ⌊(n : ℝ) * u ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n) :
          EuclideanSpace ℝ (Fin k)))
      = gaussVec (fun i : Fin k ↦
          Real.sqrt ((⌊(n : ℝ) * u ((i : ℕ) + 1)⌋₊ : ℝ) / n - (⌊(n : ℝ) * u (i : ℕ)⌋₊ : ℝ) / n)) := by
  classical
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set m : ℕ → ℕ := fun i ↦ ⌊(n : ℝ) * u i⌋₊ with hm
  have hmmono : Monotone m := fun a b hab ↦ Nat.floor_le_floor (by nlinarith [humono hab])
  have hm0 : m 0 = 0 := by simp [hm, hu0]
  set h : ℕ → ℝ := fun i ↦ (m i : ℝ) / n with hh
  have hhmono : Monotone h := by
    intro a b hab
    have : (m a : ℝ) ≤ m b := by exact_mod_cast hmmono hab
    simp only [hh]
    gcongr
  set A : Fin k → ℕ → ℝ := fun j i ↦ if i < m ((j : ℕ) + 1) then (Real.sqrt n)⁻¹ else 0 with hA
  set N : ℕ := m k with hN
  have hmle : ∀ j : Fin k, m ((j : ℕ) + 1) ≤ N := fun j ↦ hmmono (by omega)
  have hfun : (fun ω ↦ (toLp 2 (fun j : Fin k ↦
      (∑ i ∈ Finset.range (m ((j : ℕ) + 1)), X i ω) / Real.sqrt n) : EuclideanSpace ℝ (Fin k)))
      = (fun ω ↦ (toLp 2 (fun j : Fin k ↦ ∑ i ∈ Finset.range N, A j i * X i ω) :
        EuclideanSpace ℝ (Fin k))) := by
    funext ω
    congr 1
    funext j
    have hstep : ∀ i, A j i * X i ω
        = if i < m ((j : ℕ) + 1) then (Real.sqrt n)⁻¹ * X i ω else 0 := by
      intro i; simp only [hA]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun i _ ↦ hstep i), ← Finset.sum_filter]
    have hf : (Finset.range N).filter (fun i ↦ i < m ((j : ℕ) + 1))
        = Finset.range (m ((j : ℕ) + 1)) := by
      have := hmle j; ext x; simp; omega
    rw [hf, ← Finset.mul_sum, inv_mul_eq_div]
  rw [show (fun ω ↦ (toLp 2 (fun j : Fin k ↦
      (∑ i ∈ Finset.range ⌊(n : ℝ) * u ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n) :
        EuclideanSpace ℝ (Fin k)))
      = (fun ω ↦ (toLp 2 (fun j : Fin k ↦
      (∑ i ∈ Finset.range (m ((j : ℕ) + 1)), X i ω) / Real.sqrt n) :
        EuclideanSpace ℝ (Fin k))) from rfl, hfun,
    show (fun i : Fin k ↦ Real.sqrt ((⌊(n : ℝ) * u ((i : ℕ) + 1)⌋₊ : ℝ) / n
      - (⌊(n : ℝ) * u (i : ℕ)⌋₊ : ℝ) / n))
      = (fun i : Fin k ↦ Real.sqrt (h ((i : ℕ) + 1) - h (i : ℕ))) from rfl]
  refine map_eq_gaussVec hindep hmeas hlaw (Finset.range N) A _ ?_
  intro j j'
  rw [covStep_sqrt_diff h hhmono j j']
  have hstep : ∀ i, ((1:ℝ≥0):ℝ) * A j i * A j' i
      = if i < min (m ((j : ℕ) + 1)) (m ((j' : ℕ) + 1)) then ((Real.sqrt n)⁻¹) ^ 2 else 0 := by
    intro i
    simp only [hA]
    by_cases h1 : i < m ((j : ℕ) + 1) <;> by_cases h2 : i < m ((j' : ℕ) + 1) <;>
      simp [h1, h2, sq]
  have hmin : min (m ((j : ℕ) + 1)) (m ((j' : ℕ) + 1)) = m (((min j j' : Fin k) : ℕ) + 1) := by
    rcases le_total j j' with hle | hle
    · rw [min_eq_left hle, min_eq_left (hmmono (Nat.succ_le_succ (Fin.le_def.mp hle)))]
    · rw [min_eq_right hle, min_eq_right (hmmono (Nat.succ_le_succ (Fin.le_def.mp hle)))]
  have hfilter : (Finset.range N).filter (fun i ↦ i < min (m ((j : ℕ) + 1)) (m ((j' : ℕ) + 1)))
      = Finset.range (min (m ((j : ℕ) + 1)) (m ((j' : ℕ) + 1))) := by
    have h1 := hmle j; have h2 := hmle j'
    ext x; simp; omega
  have hsq : ((Real.sqrt n)⁻¹) ^ 2 = 1 / (n : ℝ) := by
    rw [inv_pow, Real.sq_sqrt hnpos.le]; ring
  rw [Finset.sum_congr rfl (fun i _ ↦ hstep i), ← Finset.sum_filter, hfilter, Finset.sum_const,
    Finset.card_range, hmin, hsq]
  simp only [hh, hm0, nsmul_eq_mul, Nat.cast_zero, zero_div, sub_zero]
  ring

/-- The law of a Brownian motion sampled at times `u 1 ≤ u 2 ≤ ...`. -/
