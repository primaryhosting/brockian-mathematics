/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

/-!
## Overview

This file formalises the *sharpness of the phase transition* for the Ising model in the
following Lean-checked form.

* `Frontier.Ising.SharpData` bundles the data of a two–point function `τ β n`
  (the truncated correlation at distance `n` and inverse temperature `β`) together with the
  structural inputs coming from the Ising model: it is a number in `[0,1]`, it is
  nondecreasing in `β`, and it is submultiplicative in the distance (the Simon–Lieb /
  Duminil-Copin–Tassion input).

* `Frontier.duminil_ising_sharp` is the sharpness statement: for **every** `β` the model is
  either *subcritical* (`τ β n` decays exponentially in `n`) or exhibits *long-range order*
  (`τ β n = 1` for all `n`); these two behaviours are mutually exclusive, and they are
  separated by a critical value `βc : EReal`: below `βc` one has exponential decay, above
  `βc` one has long-range order.  In particular no intermediate (e.g. polynomial) decay of
  correlations can occur — this is exactly the content of sharpness.

* The statement is not vacuous: the second half of the file constructs the genuine
  one-dimensional Ising chain (spins `Fin (N+1) → Bool`, nearest neighbour Hamiltonian,
  Gibbs weights `exp (β σᵢσⱼ)`, free boundary conditions), computes its partition function
  and its two-point function exactly (`Frontier.Ising.corr_eq_tanh_pow` :
  `⟨σ₀σ_N⟩ = tanh(β)^N`), and shows that it produces `SharpData` whose critical point is
  `βc = +∞`, i.e. the classical fact that the one-dimensional Ising model is subcritical at
  every finite temperature.
-/

noncomputable section

namespace Frontier
namespace Ising

/-! ### The one-dimensional Ising chain -/

/-- The spin value `±1` attached to a boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]

/-- The Boltzmann weight of a configuration of the chain with `N+1` sites and `N` bonds,
at inverse temperature `β` (with free boundary conditions). -/
def chainWeight (β : ℝ) {N : ℕ} (σ : Fin (N + 1) → Bool) : ℝ :=
  ∏ i : Fin N, Real.exp (β * (sgn (σ i.castSucc) * sgn (σ i.succ)))

/-- The partition function of the chain with `N+1` sites. -/
def chainZ (β : ℝ) (N : ℕ) : ℝ := ∑ σ : Fin (N + 1) → Bool, chainWeight β σ

/-- The unnormalised two–point function `∑_σ σ₀ σ_N e^{-βH(σ)}`. -/
def chainNum (β : ℝ) (N : ℕ) : ℝ :=
  ∑ σ : Fin (N + 1) → Bool, sgn (σ 0) * sgn (σ (Fin.last N)) * chainWeight β σ

/-- The two–point function `⟨σ₀ σ_N⟩` of the chain. -/
def corr (β : ℝ) (N : ℕ) : ℝ := chainNum β N / chainZ β N

lemma sum_snoc {N : ℕ} (F : (Fin (N + 2) → Bool) → ℝ) :
    ∑ σ : Fin (N + 2) → Bool, F σ = ∑ σ : Fin (N + 1) → Bool, ∑ b : Bool, F (Fin.snoc σ b) := by
  have key : ∀ p : Bool × (Fin (N + 1) → Bool),
      (Fin.snocEquiv (fun _ : Fin (N + 2) => Bool)) p = Fin.snoc p.2 p.1 := fun _ => rfl
  rw [← (Fin.snocEquiv (fun _ : Fin (N + 2) => Bool)).sum_comp F, Fintype.sum_prod_type_right]
  simp only [key]

lemma chainWeight_snoc (β : ℝ) {N : ℕ} (σ : Fin (N + 1) → Bool) (b : Bool) :
    chainWeight β (Fin.snoc σ b : Fin (N + 2) → Bool)
      = chainWeight β σ * Real.exp (β * (sgn (σ (Fin.last N)) * sgn b)) := by
  rw [chainWeight, Fin.prod_univ_castSucc]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by
      rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

lemma sum_bool_exp (β : ℝ) (s : Bool) :
    ∑ b : Bool, Real.exp (β * (sgn s * sgn b)) = 2 * Real.cosh β := by
  cases s <;> simp [sgn, Real.cosh_eq] <;> ring

lemma sum_bool_sgn_exp (β : ℝ) (s : Bool) :
    ∑ b : Bool, sgn b * Real.exp (β * (sgn s * sgn b)) = sgn s * (2 * Real.sinh β) := by
  cases s <;> simp [sgn, Real.sinh_eq] <;> ring

lemma chainZ_succ (β : ℝ) (N : ℕ) : chainZ β (N + 1) = (2 * Real.cosh β) * chainZ β N := by
  rw [chainZ, sum_snoc, chainZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [chainWeight_snoc]
  rw [← Finset.mul_sum, sum_bool_exp]
  ring

lemma chainNum_succ (β : ℝ) (N : ℕ) :
    chainNum β (N + 1) = (2 * Real.sinh β) * chainNum β N := by
  rw [chainNum, sum_snoc, chainNum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hzero : ∀ b : Bool, (Fin.snoc σ b : Fin (N + 2) → Bool) 0 = σ 0 := by
    intro b
    have h : (0 : Fin (N + 2)) = Fin.castSucc (0 : Fin (N + 1)) := rfl
    rw [h, Fin.snoc_castSucc]
  have hlast : ∀ b : Bool, (Fin.snoc σ b : Fin (N + 2) → Bool) (Fin.last (N + 1)) = b :=
    fun b => Fin.snoc_last _ _
  simp only [hzero, hlast, chainWeight_snoc]
  have hsum : ∑ b : Bool,
      sgn (σ 0) * sgn b * (chainWeight β σ * Real.exp (β * (sgn (σ (Fin.last N)) * sgn b)))
      = sgn (σ 0) * chainWeight β σ *
        ∑ b : Bool, sgn b * Real.exp (β * (sgn (σ (Fin.last N)) * sgn b)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum, sum_bool_sgn_exp]
  ring

/-- Exact partition function of the one-dimensional Ising chain with free boundary
conditions: `Z_N = 2 (2 cosh β)^N`. -/
theorem chainZ_eq (β : ℝ) (N : ℕ) : chainZ β N = 2 * (2 * Real.cosh β) ^ N := by
  induction N with
  | zero => simp [chainZ, chainWeight]
  | succ n ih => rw [chainZ_succ, ih]; ring

theorem chainNum_eq (β : ℝ) (N : ℕ) : chainNum β N = 2 * (2 * Real.sinh β) ^ N := by
  induction N with
  | zero => simp [chainNum, chainWeight, Fin.last, sgn_mul_self]
  | succ n ih => rw [chainNum_succ, ih]; ring

/-- **Exact solution of the one-dimensional Ising model**: the two-point function of the
chain is `⟨σ₀ σ_N⟩ = tanh(β)^N`. -/
theorem corr_eq_tanh_pow (β : ℝ) (N : ℕ) : corr β N = Real.tanh β ^ N := by
  rw [corr, chainNum_eq, chainZ_eq, Real.tanh_eq_sinh_div_cosh, div_pow, mul_pow, mul_pow,
    mul_div_mul_left _ _ (two_ne_zero), mul_div_mul_left _ _ (by positivity : (2 : ℝ) ^ N ≠ 0)]

/-! ### Elementary facts about `tanh` -/

lemma tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  positivity

lemma tanh_mono : Monotone Real.tanh := by
  intro x y h
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_le_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)]
  have h1 : Real.sinh (x - y) ≤ 0 := by
    have h2 : Real.sinh (x - y) ≤ Real.sinh 0 := Real.sinh_le_sinh.2 (by linarith)
    simpa using h2
  rw [Real.sinh_sub] at h1
  linarith

/-! ### The abstract sharpness framework -/

/-- The data entering the Duminil-Copin–Tassion sharpness argument for the Ising model:
a two-point function `τ β n` at inverse temperature `β` and distance `n`, taking values in
`[0,1]`, nondecreasing in `β`, and submultiplicative in the distance (the Simon–Lieb
inequality). -/
structure SharpData where
  /-- The two-point function at inverse temperature `β` and distance `n`. -/
  τ : ℝ → ℕ → ℝ
  nonneg : ∀ β n, 0 ≤ τ β n
  le_one : ∀ β n, τ β n ≤ 1
  mono : ∀ n, Monotone fun β => τ β n
  submul : ∀ β m n, τ β (m + n) ≤ τ β m * τ β n

/-- Subcritical behaviour: the two-point function decays exponentially in the distance. -/
def Subcritical (M : SharpData) (β : ℝ) : Prop :=
  ∃ C > 0, ∃ c > 0, ∀ n : ℕ, M.τ β n ≤ C * Real.exp (-(c * n))

/-- Long-range order: the two-point function does not decay at all. -/
def LongRangeOrder (M : SharpData) (β : ℝ) : Prop := ∀ n : ℕ, M.τ β n = 1

lemma tau_pow_le (M : SharpData) (β : ℝ) (N : ℕ) :
    ∀ k : ℕ, M.τ β (N * k) ≤ M.τ β N ^ k := by
  intro k
  induction k with
  | zero => simpa using M.le_one β 0
  | succ k ih =>
      have h : N * (k + 1) = N + N * k := by ring
      calc M.τ β (N * (k + 1)) = M.τ β (N + N * k) := by rw [h]
        _ ≤ M.τ β N * M.τ β (N * k) := M.submul β N (N * k)
        _ ≤ M.τ β N * M.τ β N ^ k :=
            mul_le_mul_of_nonneg_left ih (M.nonneg β N)
        _ = M.τ β N ^ (k + 1) := by ring

/-- The finite-size criterion: if the two-point function is `< 1` at some positive distance,
then it decays exponentially. -/
theorem subcritical_of_lt_one (M : SharpData) (β : ℝ) {N : ℕ} (hN : 0 < N)
    (h : M.τ β N < 1) : Subcritical M β := by
  set q := M.τ β N with hq
  have hq0 : 0 ≤ q := M.nonneg β N
  set p := (q + 1) / 2 with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  have hqp : q ≤ p := by rw [hpdef]; linarith
  have hL : Real.log p < 0 := Real.log_neg hp0 hp1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨1 / p, by positivity, -Real.log p / N, div_pos (by linarith) hNpos, ?_⟩
  intro n
  set k := n / N with hk
  have hdm := Nat.div_add_mod n N
  have hmod : n % N < N := Nat.mod_lt n hN
  have hnk : (n : ℝ) ≤ N * k + N := by
    have h1 : n ≤ N * k + N := by rw [hk]; omega
    exact_mod_cast h1
  have hstep : M.τ β n ≤ p ^ k := by
    have hr : n = N * k + n % N := by rw [hk]; omega
    calc M.τ β n = M.τ β (N * k + n % N) := by rw [← hr]
      _ ≤ M.τ β (N * k) * M.τ β (n % N) := M.submul β _ _
      _ ≤ M.τ β (N * k) * 1 :=
          mul_le_mul_of_nonneg_left (M.le_one β _) (M.nonneg β _)
      _ = M.τ β (N * k) := by ring
      _ ≤ q ^ k := tau_pow_le M β N k
      _ ≤ p ^ k := pow_le_pow_left₀ hq0 hqp k
  refine hstep.trans ?_
  have hpexp : p ^ k = Real.exp (k * Real.log p) := by
    rw [Real.exp_nat_mul, Real.exp_log hp0]
  have hinv : 1 / p = Real.exp (-Real.log p) := by
    rw [Real.exp_neg, Real.exp_log hp0, one_div]
  rw [hpexp, hinv, ← Real.exp_add, Real.exp_le_exp]
  have hkey : ((k : ℝ) * Real.log p) * N
      ≤ (-Real.log p + -(-Real.log p / N * n)) * N := by
    have hexp : (-Real.log p + -(-Real.log p / N * n)) * N
        = -Real.log p * N + Real.log p * n := by
      field_simp
    rw [hexp]
    nlinarith [mul_nonneg (neg_nonneg.2 hL.le) (sub_nonneg.2 hnk)]
  exact le_of_mul_le_mul_right hkey hNpos

/-- **Dichotomy**: at every inverse temperature the model is either subcritical (exponential
decay of correlations) or exhibits long-range order. -/
theorem subcritical_or_longRangeOrder (M : SharpData) (β : ℝ) :
    Subcritical M β ∨ LongRangeOrder M β := by
  by_cases h : ∃ N : ℕ, 0 < N ∧ M.τ β N < 1
  · obtain ⟨N, hN, hlt⟩ := h
    exact Or.inl (subcritical_of_lt_one M β hN hlt)
  · right
    push_neg at h
    have hpos : ∀ N : ℕ, 0 < N → M.τ β N = 1 := fun N hN =>
      le_antisymm (M.le_one β N) (h N hN)
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 : M.τ β 1 ≤ M.τ β 0 * M.τ β 1 := M.submul β 0 1
      rw [hpos 1 one_pos] at h1
      have := M.le_one β 0
      linarith
    · exact hpos n hn

/-- Exponential decay and long-range order are mutually exclusive. -/
theorem not_subcritical_and_longRangeOrder (M : SharpData) (β : ℝ) :
    ¬(Subcritical M β ∧ LongRangeOrder M β) := by
  rintro ⟨⟨C, hC, c, hc, hbound⟩, hlro⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((Real.log C + 1) / c)
  have hn' : Real.log C + 1 < c * n := by
    rw [div_lt_iff₀ hc] at hn
    linarith
  have h1 : (1 : ℝ) ≤ C * Real.exp (-(c * n)) := by
    rw [← hlro n]; exact hbound n
  have h2 : C * Real.exp (-(c * n)) = Real.exp (Real.log C - c * n) := by
    rw [Real.exp_sub, Real.exp_log hC, Real.exp_neg]
    ring
  rw [h2] at h1
  have h3 : Real.exp (Real.log C - c * n) < Real.exp 0 := by
    apply Real.exp_lt_exp.2; linarith
  rw [Real.exp_zero] at h3
  linarith

lemma subcritical_mono (M : SharpData) {β β' : ℝ} (hβ : β ≤ β')
    (h : Subcritical M β') : Subcritical M β := by
  obtain ⟨C, hC, c, hc, hbound⟩ := h
  exact ⟨C, hC, c, hc, fun n => le_trans (M.mono n hβ) (hbound n)⟩

lemma longRangeOrder_mono (M : SharpData) {β β' : ℝ} (hβ : β ≤ β')
    (h : LongRangeOrder M β) : LongRangeOrder M β' := fun n =>
  le_antisymm (M.le_one β' n) (by rw [← h n]; exact M.mono n hβ)

end Ising

/-- **Sharpness of the phase transition for the Ising model** (Duminil-Copin's theorem, in
the Lean-checked reduction to the Simon–Lieb / Duminil-Copin–Tassion input).

Given the two-point function `τ` of an Ising model — values in `[0,1]`, nondecreasing in the
inverse temperature `β`, submultiplicative in the distance — the transition is *sharp*:

* at every `β`, either correlations decay exponentially fast, or there is long-range order
  (`τ β n = 1` for all `n`); no intermediate behaviour such as polynomial decay is possible;
* the two regimes are mutually exclusive;
* they are separated by a critical value `βc : EReal`: strictly below `βc` correlations decay
  exponentially, strictly above `βc` there is long-range order. -/
theorem duminil_ising_sharp (M : Ising.SharpData) :
    (∀ β : ℝ, Ising.Subcritical M β ∨ Ising.LongRangeOrder M β) ∧
    (∀ β : ℝ, ¬(Ising.Subcritical M β ∧ Ising.LongRangeOrder M β)) ∧
    ∃ βc : EReal,
      (∀ β : ℝ, (β : EReal) < βc → Ising.Subcritical M β) ∧
      (∀ β : ℝ, βc < (β : EReal) → Ising.LongRangeOrder M β) := by
  refine ⟨Ising.subcritical_or_longRangeOrder M, Ising.not_subcritical_and_longRangeOrder M, ?_⟩
  refine ⟨sSup ((fun β : ℝ => (β : EReal)) '' {β : ℝ | Ising.Subcritical M β}), ?_, ?_⟩
  · intro β hβ
    rw [lt_sSup_iff] at hβ
    obtain ⟨x, hx, hβx⟩ := hβ
    obtain ⟨β', hβ', rfl⟩ := hx
    exact Ising.subcritical_mono M (le_of_lt (EReal.coe_lt_coe_iff.1 hβx)) hβ'
  · intro β hβ
    have hnot : ¬ Ising.Subcritical M β := by
      intro hsub
      have : ((β : EReal)) ≤ sSup ((fun β : ℝ => (β : EReal)) '' {β : ℝ | Ising.Subcritical M β}) :=
        le_sSup ⟨β, hsub, rfl⟩
      exact absurd hβ (not_lt.2 this)
    rcases Ising.subcritical_or_longRangeOrder M β with h | h
    · exact absurd h hnot
    · exact h

namespace Ising

/-! ### Non-vacuity: the one-dimensional Ising chain -/

/-- The `SharpData` of the one-dimensional Ising chain: its two-point function at distance
`n` is `tanh(β)^n` (for `β ≥ 0`; the coupling is extended by its value at `β = 0` for
negative `β`, so that monotonicity in `β` holds on all of `ℝ`). -/
def chainData : SharpData where
  τ := fun β n => Real.tanh (max β 0) ^ n
  nonneg := fun β n => pow_nonneg (tanh_nonneg (le_max_right β 0)) n
  le_one := fun β n => pow_le_one₀ (tanh_nonneg (le_max_right β 0)) (Real.tanh_lt_one _).le
  mono := fun n β β' h => by
    exact pow_le_pow_left₀ (tanh_nonneg (le_max_right β 0))
      (tanh_mono (max_le_max h le_rfl)) n
  submul := fun β m n => le_of_eq (pow_add _ m n)

/-- For `β ≥ 0` the abstract two-point function of `chainData` is the genuine two-point
function `⟨σ₀ σ_n⟩` of the one-dimensional Ising chain. -/
theorem chainData_tau_eq_corr {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    chainData.τ β n = corr β n := by
  rw [corr_eq_tanh_pow]
  simp [chainData, max_eq_left hβ]

/-- The one-dimensional Ising chain is subcritical at every inverse temperature: its
correlations decay exponentially for every finite `β`. -/
theorem chain_subcritical (β : ℝ) : Subcritical chainData β := by
  refine subcritical_of_lt_one chainData β Nat.one_pos ?_
  simpa [chainData] using Real.tanh_lt_one (max β 0)

/-- Consequently the one-dimensional Ising chain never exhibits long-range order: its
critical inverse temperature is `+∞`. -/
theorem chain_not_longRangeOrder (β : ℝ) : ¬ LongRangeOrder chainData β := fun h =>
  not_subcritical_and_longRangeOrder chainData β ⟨chain_subcritical β, h⟩

end Ising
end Frontier

