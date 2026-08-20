/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
## Dependency graph

The target `Brockian.BetrothedNumbers.density_zero_reduction` is the *reduction* step of
Pollack's theorem "quasi-amicable (betrothed) numbers are rare": the set of integers belonging
to a betrothed pair has asymptotic density zero.

```
                       density_zero_reduction
                                 |
                                 v
        hasDensityZero_of_counting_le_div          (analytic core, proved here)
                     |                    \
                     v                     v
   tendsto_sqrt_log_atTop (proved)     squeeze / order lemmas (Mathlib)
                     |
                     v
   Real.tendsto_log_atTop, Real.tendsto_sqrt_atTop (Mathlib)
```

Unproved input (the *only* hypothesis, isolated as `PollackBound`):

```
  PollackBound :  #{ n < x : n is betrothed } ≪ x / sqrt (log x)
```

which in turn is where the genuinely hard analytic number theory of Pollack's paper lives
(sieve bounds for `σ(n) = m + n + 1`, normal order of `ω`, Erdős' method for amicable numbers).
Everything else in this file is proved unconditionally:

* `Brockian.BetrothedNumbers.Betrothed`, `betrothedSet`, `counting`, `HasDensityZero` — definitions;
* `counting_mono`, `counting_le`                   — elementary counting bounds;
* `hasDensityZero_mono`                            — density zero passes to subsets;
* `hasDensityZero_iff_isLittleO`                   — reformulation as `N(x) = o(x)`;
* `hasDensityZero_of_counting_le_div`              — the weakest reusable analytic lemma:
    an eventual bound `N(x) ≤ C * x / g x` with `g → ∞` forces density zero;
* `tendsto_sqrt_log_atTop`                         — `√(log x) → ∞` along `ℕ`;
* `Betrothed.symm`, `Betrothed.sigma_eq`, `sigma_gt_succ_of_mem`,
  `not_prime_of_mem`, `one_notMem`, `zero_notMem` — unconditional structure of betrothed numbers;
* `betrothed_48_75`                                — the pair `(48, 75)` is betrothed, so the
    reduction below is not vacuous.

No density statement is claimed unconditionally: `density_zero_reduction` has `PollackBound`
as an explicit hypothesis.
-/

namespace Brockian
namespace BetrothedNumbers

open Filter Asymptotics ArithmeticFunction
open scoped Topology

/-! ## Definitions -/

/-- `Betrothed m n` says that `m` and `n` form a *betrothed* (quasi-amicable) pair:
they are distinct positive integers with `σ(m) = σ(n) = m + n + 1`, i.e. each is the sum of
the *nontrivial* divisors (proper divisors excluding `1`) of the other. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- The set of integers belonging to some betrothed pair. -/
def betrothedSet : Set ℕ := {n | ∃ m, Betrothed m n}

/-- Counting function of a set of naturals: the number of its elements below `x`. -/
noncomputable def counting (S : Set ℕ) (x : ℕ) : ℕ := (S ∩ Set.Iio x).ncard

/-- A set of naturals has asymptotic density zero. -/
def HasDensityZero (S : Set ℕ) : Prop :=
  Tendsto (fun x : ℕ => (counting S x : ℝ) / (x : ℝ)) atTop (𝓝 0)

/-- Pollack's quantitative bound for betrothed numbers: the counting function of the
betrothed numbers is `O (x / √(log x))`.  This is the (unproved) analytic input. -/
def PollackBound : Prop :=
  ∃ C : ℝ, ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    (counting betrothedSet x : ℝ) ≤ C * (x : ℝ) / Real.sqrt (Real.log x)

/-! ## Elementary counting lemmas -/

theorem finite_inter_Iio (S : Set ℕ) (x : ℕ) : (S ∩ Set.Iio x).Finite :=
  (Set.finite_Iio x).subset Set.inter_subset_right

theorem counting_mono {S T : Set ℕ} (h : S ⊆ T) (x : ℕ) : counting S x ≤ counting T x :=
  Set.ncard_le_ncard (Set.inter_subset_inter_left _ h) (finite_inter_Iio T x)

theorem counting_le (S : Set ℕ) (x : ℕ) : counting S x ≤ x := by
  have h : counting S x ≤ (Set.Iio x).ncard :=
    Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Iio x)
  rwa [Set.ncard_Iio_nat] at h

/-! ## Reusable density-zero lemmas -/

/-- Density zero passes to subsets. -/
theorem hasDensityZero_mono {S T : Set ℕ} (hST : S ⊆ T) (hT : HasDensityZero T) :
    HasDensityZero S := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => (0 : ℝ))
    (h := fun x : ℕ => (counting T x : ℝ) / (x : ℝ)) tendsto_const_nhds hT ?_ ?_
  · filter_upwards with x
    positivity
  · filter_upwards with x
    have hle : (counting S x : ℝ) ≤ (counting T x : ℝ) := by exact_mod_cast counting_mono hST x
    gcongr

/-- Density zero is exactly the statement `N(x) = o(x)`. -/
theorem hasDensityZero_iff_isLittleO (S : Set ℕ) :
    HasDensityZero S ↔
      (fun x : ℕ => (counting S x : ℝ)) =o[atTop] (fun x : ℕ => (x : ℝ)) := by
  rw [Asymptotics.isLittleO_iff_tendsto]
  · rfl
  · intro x hx
    have : x = 0 := by exact_mod_cast hx
    subst this
    simp [counting]

/-- **The weakest reusable analytic lemma.**  If the counting function of `S` is eventually
bounded by `C * x / g x` for some function `g` tending to infinity, then `S` has density zero. -/
theorem hasDensityZero_of_counting_le_div {S : Set ℕ} {g : ℕ → ℝ} {C : ℝ} {X : ℕ}
    (hg : Tendsto g atTop atTop)
    (hbound : ∀ x : ℕ, X ≤ x → (counting S x : ℝ) ≤ C * (x : ℝ) / g x) :
    HasDensityZero S := by
  have hgtop : ∀ᶠ x : ℕ in atTop, 1 ≤ g x := hg.eventually_ge_atTop 1
  have hCg : Tendsto (fun x : ℕ => C / g x) atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.div_atTop (f := fun _ : ℕ => C) tendsto_const_nhds hg)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => (0 : ℝ))
    (h := fun x : ℕ => C / g x) tendsto_const_nhds hCg ?_ ?_
  · filter_upwards with x
    positivity
  · filter_upwards [hgtop, Filter.eventually_ge_atTop X, Filter.eventually_ge_atTop 1] with
      x hgx hXx hx1
    have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
    have hgpos : (0 : ℝ) < g x := lt_of_lt_of_le zero_lt_one hgx
    have h := hbound x hXx
    rw [div_le_iff₀ hxpos]
    calc (counting S x : ℝ) ≤ C * (x : ℝ) / g x := h
      _ = C / g x * (x : ℝ) := by field_simp

/-- `√(log x) → ∞` along the naturals. -/
theorem tendsto_sqrt_log_atTop :
    Tendsto (fun x : ℕ => Real.sqrt (Real.log x)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-! ## Unconditional structure of betrothed numbers -/

theorem Betrothed.symm {m n : ℕ} (h : Betrothed m n) : Betrothed n m := by
  obtain ⟨hm, hn, hmn, h1, h2⟩ := h
  refine ⟨hn, hm, hmn.symm, ?_, ?_⟩ <;> omega

theorem Betrothed.sigma_eq {m n : ℕ} (h : Betrothed m n) : sigma 1 m = sigma 1 n := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  omega

/-- For a betrothed number `n` one has `σ(n) > n + 1`; in particular `n` is abundant-ish. -/
theorem sigma_gt_succ_of_mem {n : ℕ} (hn : n ∈ betrothedSet) : n + 1 < sigma 1 n := by
  obtain ⟨m, hm, hn0, hmn, h1, h2⟩ := hn
  omega

theorem zero_notMem : (0 : ℕ) ∉ betrothedSet := by
  rintro ⟨m, -, h, -⟩
  exact absurd h (lt_irrefl 0)

theorem one_notMem : (1 : ℕ) ∉ betrothedSet := by
  intro h
  have := sigma_gt_succ_of_mem h
  simp at this

/-- Betrothed numbers are never prime. -/
theorem not_prime_of_mem {n : ℕ} (hn : n ∈ betrothedSet) : ¬ n.Prime := by
  intro hp
  have hσ : sigma 1 n = n + 1 := by
    rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors]
  have := sigma_gt_succ_of_mem hn
  omega

/-- The smallest betrothed pair `(48, 75)`: `σ(48) = σ(75) = 124 = 48 + 75 + 1`.
In particular `betrothedSet` is nonempty, so the reduction below is not vacuous. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    · rw [ArithmeticFunction.sigma_one_apply]; decide

theorem mem_betrothedSet_75 : (75 : ℕ) ∈ betrothedSet := ⟨48, betrothed_48_75⟩

/-! ## The reduction -/

/-- **Density zero reduction for betrothed numbers.**

Granting Pollack's quantitative bound `#{n < x : n betrothed} ≪ x / √(log x)`
(the hypothesis `PollackBound`, which is the hard analytic input of Pollack's theorem),
the set of betrothed (quasi-amicable) numbers has asymptotic density zero:
`#{n < x : n betrothed} / x → 0`.

The reduction itself is proved unconditionally here, via the reusable lemma
`hasDensityZero_of_counting_le_div` together with `tendsto_sqrt_log_atTop`. -/
theorem density_zero_reduction (h : PollackBound) : HasDensityZero betrothedSet := by
  obtain ⟨C, X, hC⟩ := h
  exact hasDensityZero_of_counting_le_div tendsto_sqrt_log_atTop hC

end BetrothedNumbers
end Brockian

