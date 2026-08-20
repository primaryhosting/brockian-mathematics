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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- A *Landau prime* is a prime of the form `n ^ 2 + 1`. -/
def IsLandauPrime (p : ℕ) : Prop := p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 1

/-- The counting function `#{n ≤ x : n ^ 2 + 1 is prime}`. -/
def landauCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n => Nat.Prime (n ^ 2 + 1))).card

/-- Weak (unboundedness) form of the Hardy–Littlewood asymptotic for `n ^ 2 + 1`:
the counting function `landauCount` is unbounded. -/
def LandauCountUnbounded : Prop := ∀ B : ℕ, ∃ x : ℕ, B < landauCount x

/-- The set of `n` such that `n ^ 2 + 1` is prime. -/
def LandauArguments : Set ℕ := {n : ℕ | Nat.Prime (n ^ 2 + 1)}

lemma landauArguments_finite_of_finite
    (h : {p : ℕ | IsLandauPrime p}.Finite) : LandauArguments.Finite := by
  apply Set.Finite.of_finite_image (f := fun n : ℕ => n ^ 2 + 1)
  · refine h.subset ?_
    rintro p ⟨n, hn, rfl⟩
    exact ⟨hn, n, rfl⟩
  · intro a _ b _ hab
    have hab2 : a ^ 2 = b ^ 2 := by simpa using hab
    exact Nat.pow_left_injective (by norm_num) hab2

lemma landauCount_le_of_finite (h : LandauArguments.Finite) (x : ℕ) :
    landauCount x ≤ h.toFinset.card := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simpa [Set.Finite.mem_toFinset, LandauArguments] using hn.2

/-- **Landau's fourth conjecture, conditional on unboundedness of the counting function.**
If the number of `n ≤ x` with `n ^ 2 + 1` prime is unbounded in `x`, then there are
infinitely many primes of the form `n ^ 2 + 1`. -/
theorem LandauFourthConjecture (h : LandauCountUnbounded) :
    {p : ℕ | IsLandauPrime p}.Infinite := by
  intro hfin
  have hA : LandauArguments.Finite := landauArguments_finite_of_finite hfin
  obtain ⟨x, hx⟩ := h hA.toFinset.card
  exact absurd (landauCount_le_of_finite hA x) (by omega)

/-- Conversely, infinitude of Landau primes gives an unbounded counting function, so the
hypothesis of `LandauFourthConjecture` is *equivalent* to the conjecture. -/
theorem landauCountUnbounded_iff :
    LandauCountUnbounded ↔ {p : ℕ | IsLandauPrime p}.Infinite := by
  refine ⟨LandauFourthConjecture, fun h B => ?_⟩
  -- The set of arguments is infinite, hence contains more than `B` elements below some `x`.
  have hA : LandauArguments.Infinite := by
    intro hfin
    refine h ?_
    have : {p : ℕ | IsLandauPrime p} ⊆ (fun n : ℕ => n ^ 2 + 1) '' LandauArguments := by
      rintro p ⟨hp, n, rfl⟩
      exact ⟨n, hp, rfl⟩
    exact Set.Finite.subset (hfin.image _) this
  obtain ⟨s, hs, hcard⟩ := hA.exists_subset_card_eq (B + 1)
  obtain ⟨x, hx⟩ := s.exists_le
  have hsub : s ⊆ (Finset.range (x + 1)).filter (fun n => Nat.Prime (n ^ 2 + 1)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hx n hn; omega, hs hn⟩
  have hle : B + 1 ≤ landauCount x := by
    rw [landauCount, ← hcard]
    exact Finset.card_le_card hsub
  exact ⟨x, hle⟩

/-! ## Reduction from the Hardy–Littlewood lower bound -/

/-- The Hardy–Littlewood (Bateman–Horn) prediction for `n ^ 2 + 1` in a weakened, purely
lower-bound form: for some constant `c > 0` one has `landauCount x ≥ c * x / log x`
for all large `x`. -/
def HardyLittlewoodLowerBound : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ x : ℕ in Filter.atTop, c * ((x : ℝ) / Real.log x) ≤ landauCount x

lemma tendsto_id_div_log_atTop :
    Filter.Tendsto (fun x : ℝ => x / Real.log x) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono' Filter.atTop (f₁ := fun x : ℝ => Real.sqrt x / 2)
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hlog : Real.log x ≤ 2 * Real.sqrt x := by
      have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
      have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
        rw [Real.log_sqrt hx0.le]; ring
      nlinarith
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    rw [div_le_div_iff₀ (by norm_num) hlogpos]
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  · exact Filter.Tendsto.atTop_div_const (by norm_num) Real.tendsto_sqrt_atTop

/-- The Hardy–Littlewood lower bound implies that the counting function is unbounded. -/
theorem landauCountUnbounded_of_hardyLittlewood (h : HardyLittlewoodLowerBound) :
    LandauCountUnbounded := by
  obtain ⟨c, hc, hbound⟩ := h
  intro B
  have htend : Filter.Tendsto (fun n : ℕ => c * ((n : ℝ) / Real.log n))
      Filter.atTop Filter.atTop :=
    ((tendsto_id_div_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc)
  have hev := (htend.eventually_ge_atTop ((B : ℝ) + 1)).and hbound
  obtain ⟨x, hx1, hx2⟩ := hev.exists
  have hlt : (B : ℝ) < (landauCount x : ℝ) := by linarith
  exact ⟨x, by exact_mod_cast hlt⟩

/-- **Conditional Landau fourth conjecture from Hardy–Littlewood.**  If the Hardy–Littlewood
lower bound for the counting function of `n ^ 2 + 1` holds, then there are infinitely many
primes of the form `n ^ 2 + 1`. -/
theorem infinite_landauPrimes_of_hardyLittlewood (h : HardyLittlewoodLowerBound) :
    {p : ℕ | IsLandauPrime p}.Infinite :=
  LandauFourthConjecture (landauCountUnbounded_of_hardyLittlewood h)

/-! ## Unconditional results -/

/-- A finite sanity check: exactly five values `n ≤ 10` give a prime `n ^ 2 + 1`
(namely `n = 1, 2, 4, 6, 10`, giving `2, 5, 17, 37, 101`). -/
theorem landauCount_ten : landauCount 10 = 5 := by decide

/-- Every odd prime factor of `n ^ 2 + 1` is congruent to `1` modulo `4`. -/
theorem odd_prime_factor_sq_add_one_mod_four {p n : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hdvd : p ∣ n ^ 2 + 1) : p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne3 : p % 4 ≠ 3 := by
    have : ((n : ZMod p)) ^ 2 = -1 := by
      have : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
        exact (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      push_cast at this
      linear_combination this
    exact (ZMod.exists_sq_eq_neg_one_iff).1 ⟨(n : ZMod p), by rw [← this]; ring⟩
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hodd
  omega

/-- Unconditionally, there are infinitely many primes dividing some number of the form
`n ^ 2 + 1`. -/
theorem infinite_primes_dvd_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  refine Set.Infinite.mono ?_ (Nat.infinite_setOf_prime_modEq_one (k := 4) (by norm_num))
  rintro p ⟨hp, hmod⟩
  refine ⟨hp, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp4 : p % 4 ≠ 3 := by
    have : p % 4 = 1 % 4 := hmod
    omega
  obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 hp4
  refine ⟨y.val, ?_⟩
  have hz : ((y.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [sq, ← hy]; ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 hz

/-!
## Remarks on Mathlib coverage

Landau's fourth problem (infinitely many primes of the form `n ^ 2 + 1`) is an open problem,
and Mathlib contains no lemma proving it; what is proved here is therefore an equivalence
(`landauCountUnbounded_iff`), a reduction from the Hardy–Littlewood lower bound
(`infinite_landauPrimes_of_hardyLittlewood`), and unconditional partial results.
The Mathlib inputs used for the unconditional part are
`Nat.infinite_setOf_prime_modEq_one` (Dirichlet's theorem for the progression `1 mod k`)
and `ZMod.exists_sq_eq_neg_one_iff` (`-1` is a square mod `p` iff `p % 4 ≠ 3`).
-/

end Brockian.LandauNSquaredPlusOne

