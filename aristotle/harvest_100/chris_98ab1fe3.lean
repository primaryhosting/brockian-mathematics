import Brockian.GoldbachComb

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

/-
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.GoldbachComb

/-- The set of ordered Goldbach pairs of `n`: pairs of primes `(p, q)` with `p + q = n`. -/
def goldbachPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = n)

/-- Number of ordered Goldbach representations of `n`. -/
def goldbachCount (n : ℕ) : ℕ := (goldbachPairs n).card

@[simp] theorem mem_goldbachPairs {n : ℕ} {pq : ℕ × ℕ} :
    pq ∈ goldbachPairs n ↔ Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = n := by
  classical
  constructor
  · intro h
    simpa [goldbachPairs, Finset.mem_filter] using (Finset.mem_filter.mp h).2
  · rintro ⟨hp, hq, hsum⟩
    refine Finset.mem_filter.mpr ⟨?_, hp, hq, hsum⟩
    refine Finset.mem_product.mpr ⟨?_, ?_⟩ <;>
      exact Finset.mem_range.mpr (by omega)

/-- The empirical mean of `f` over the ordered Goldbach pairs of `n`
(with the convention that the mean is `0` when `n` has no Goldbach representation). -/
noncomputable def gMean (n : ℕ) (f : ℕ × ℕ → ℝ) : ℝ :=
  (∑ pq ∈ goldbachPairs n, f pq) / (goldbachPairs n).card

/-- The empirical covariance of `f` and `g` over the ordered Goldbach pairs of `n`. -/
noncomputable def gCov (n : ℕ) (f g : ℕ × ℕ → ℝ) : ℝ :=
  gMean n (fun pq => f pq * g pq) - gMean n f * gMean n g

/-- The empirical variance of `f` over the ordered Goldbach pairs of `n`. -/
noncomputable def gVar (n : ℕ) (f : ℕ × ℕ → ℝ) : ℝ := gCov n f f

theorem gMean_congr {n : ℕ} {f g : ℕ × ℕ → ℝ}
    (h : ∀ pq ∈ goldbachPairs n, f pq = g pq) : gMean n f = gMean n g := by
  unfold gMean
  rw [Finset.sum_congr rfl h]

theorem gCov_congr {n : ℕ} {f₁ f₂ g₁ g₂ : ℕ × ℕ → ℝ}
    (hf : ∀ pq ∈ goldbachPairs n, f₁ pq = f₂ pq)
    (hg : ∀ pq ∈ goldbachPairs n, g₁ pq = g₂ pq) :
    gCov n f₁ g₁ = gCov n f₂ g₂ := by
  unfold gCov
  rw [gMean_congr (fun pq hpq => by rw [hf pq hpq, hg pq hpq]), gMean_congr hf,
    gMean_congr hg]

/-- The set of ordered Goldbach pairs is invariant under swapping the two summands. -/
theorem goldbachPairs_swap (n : ℕ) :
    (goldbachPairs n).image Prod.swap = goldbachPairs n := by
  ext ⟨a, b⟩
  simp only [Finset.mem_image, mem_goldbachPairs, Prod.exists, Prod.swap_prod_mk,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x, y, ⟨hx, hy, hxy⟩, rfl, rfl⟩
    exact ⟨hy, hx, by omega⟩
  · rintro ⟨hp, hq, hsum⟩
    exact ⟨b, a, ⟨hq, hp, by omega⟩, rfl, rfl⟩

theorem gMean_swap (n : ℕ) (f : ℕ × ℕ → ℝ) :
    gMean n (fun pq => f pq.swap) = gMean n f := by
  unfold gMean
  congr 1
  conv_rhs => rw [← goldbachPairs_swap n]
  rw [Finset.sum_image (by intro a _ b _ h; simpa using congrArg Prod.swap h)]

theorem gCov_swap (n : ℕ) (f g : ℕ × ℕ → ℝ) :
    gCov n (fun pq => f pq.swap) (fun pq => g pq.swap) = gCov n f g := by
  unfold gCov
  rw [gMean_swap n f, gMean_swap n g, ← gMean_swap n (fun pq => f pq * g pq)]

/-- Swap transfer: the covariance of a statistic of the first summand with a statistic of
the second summand is unchanged when the roles of the two summands are exchanged. -/
theorem gCov_coord_swap (n : ℕ) (f g : ℕ → ℝ) :
    gCov n (fun pq => f pq.1) (fun pq => g pq.2)
      = gCov n (fun pq => f pq.2) (fun pq => g pq.1) := by
  simpa using gCov_swap n (fun pq => f pq.2) (fun pq => g pq.1)

/-- Variance transfer: the two Goldbach summands carry the same empirical variance. -/
theorem gVar_coord_swap (n : ℕ) (f : ℕ → ℝ) :
    gVar n (fun pq => f pq.1) = gVar n (fun pq => f pq.2) := by
  simpa [gVar] using gCov_swap n (fun pq => f pq.2) (fun pq => f pq.2)

/-- On the Goldbach pairs of `n`, the second coordinate is determined by the first. -/
theorem snd_eq_sub {n : ℕ} {pq : ℕ × ℕ} (h : pq ∈ goldbachPairs n) : pq.2 = n - pq.1 := by
  have := (mem_goldbachPairs.mp h).2.2
  omega

theorem fst_cast_le {n : ℕ} {pq : ℕ × ℕ} (h : pq ∈ goldbachPairs n) :
    ((pq.2 : ℕ) : ℝ) = (n : ℝ) - ((pq.1 : ℕ) : ℝ) := by
  have := (mem_goldbachPairs.mp h).2.2
  have : (pq.1 : ℝ) + (pq.2 : ℝ) = (n : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  linarith

/-- Covariance of a function of the first summand with a function of the second summand
equals the covariance obtained after reflecting the second summand through `n`; i.e. the
joint statistic is transferred to a statistic of the single coordinate `p`. -/
theorem gCov_reflect (n : ℕ) (f g : ℕ → ℝ) :
    gCov n (fun pq => f pq.1) (fun pq => g pq.2)
      = gCov n (fun pq => f pq.1) (fun pq => g (n - pq.1)) :=
  gCov_congr (fun _ _ => rfl) (fun _ hpq => by rw [snd_eq_sub hpq])

section AntiCorrelation

/-- **Perfect anti-correlation of the two Goldbach summands**: the empirical covariance of
`p` and `q` over the ordered Goldbach representations `p + q = n` is exactly minus the
variance of `p`. -/
theorem gCov_fst_snd (n : ℕ) :
    gCov n (fun pq => (pq.1 : ℝ)) (fun pq => (pq.2 : ℝ))
      = - gVar n (fun pq => (pq.1 : ℝ)) := by
  classical
  set k : ℝ := ((goldbachPairs n).card : ℝ) with hk
  set s : ℝ := ∑ pq ∈ goldbachPairs n, ((pq.1 : ℕ) : ℝ) with hs
  set q : ℝ := ∑ pq ∈ goldbachPairs n, ((pq.1 : ℕ) : ℝ) ^ 2 with hq
  have hprod : ∑ pq ∈ goldbachPairs n, ((pq.1 : ℕ) : ℝ) * ((pq.2 : ℕ) : ℝ)
      = (n : ℝ) * s - q := by
    rw [hs, hq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun pq hpq => ?_)
    rw [fst_cast_le hpq]; ring
  have hsnd : ∑ pq ∈ goldbachPairs n, ((pq.2 : ℕ) : ℝ) = (n : ℝ) * k - s := by
    rw [Finset.sum_congr rfl (fun pq hpq => fst_cast_le hpq), Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← hs, ← hk]
    ring
  simp only [gVar, gCov, gMean]
  rw [hprod, hsnd]
  simp only [← hs, ← hk]
  rcases eq_or_ne k 0 with h0 | h0
  · rw [h0]; simp
  · field_simp
    ring

end AntiCorrelation

/-- **Goldbach Covariance Transfer.**

For every `n` and all real-valued statistics `f`, `g` of a prime summand, the empirical
covariance structure on the set of ordered Goldbach representations `p + q = n` satisfies:

1. *(swap transfer)* the covariance is invariant under exchanging the roles of the two
   summands;
2. *(reflection transfer)* a covariance between the two coordinates transfers to a
   covariance of statistics of the single coordinate `p`, via `q = n - p`;
3. *(variance transfer)* the two summands carry the same empirical variance;
4. *(perfect anti-correlation)* the covariance of `p` with `q` is minus the variance of `p`.
-/
theorem GoldbachCovarianceTransfer (n : ℕ) (f g : ℕ → ℝ) :
    gCov n (fun pq => f pq.1) (fun pq => g pq.2)
        = gCov n (fun pq => f pq.2) (fun pq => g pq.1)
      ∧ gCov n (fun pq => f pq.1) (fun pq => g pq.2)
        = gCov n (fun pq => f pq.1) (fun pq => g (n - pq.1))
      ∧ gVar n (fun pq => f pq.1) = gVar n (fun pq => f pq.2)
      ∧ gCov n (fun pq => (pq.1 : ℝ)) (fun pq => (pq.2 : ℝ))
        = - gVar n (fun pq => (pq.1 : ℝ)) := by
  exact ⟨gCov_coord_swap n f g, gCov_reflect n f g, gVar_coord_swap n f, gCov_fst_snd n⟩

/-- Non-vacuity: `10` has three ordered Goldbach representations, namely
`3 + 7`, `5 + 5` and `7 + 3`. -/
theorem goldbachCount_ten : goldbachCount 10 = 3 := by
  decide

theorem goldbachPairs_ten_nonempty : (goldbachPairs 10).Nonempty := by
  rw [← Finset.card_pos]
  have : (goldbachPairs 10).card = 3 := goldbachCount_ten
  omega

theorem goldbachPairs_ten : goldbachPairs 10 = {(3, 7), (5, 5), (7, 3)} := by
  decide

/-- A concrete non-degenerate instance: for `n = 10` the variance of the first summand is
`8/3`, hence the covariance identity of `GoldbachCovarianceTransfer` has genuine content. -/
theorem gVar_ten : gVar 10 (fun pq => (pq.1 : ℝ)) = 8 / 3 := by
  simp [gVar, gCov, gMean, goldbachPairs_ten]
  norm_num

theorem gCov_ten : gCov 10 (fun pq => (pq.1 : ℝ)) (fun pq => (pq.2 : ℝ)) = -(8 / 3) := by
  rw [gCov_fst_snd 10, gVar_ten]

end Brockian.GoldbachComb

