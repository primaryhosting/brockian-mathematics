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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Brockian.Weyl.WeylLawTarget

variable {α : Type u}

/-- `countingFunction lam L K` is the number of indices `n < K` whose eigenvalue `lam n`
lies at or below the threshold `L`.  For a discrete spectrum this stabilises as `K → ∞`
and its limiting value is the Weyl counting function `N(L) = #{n | lam n ≤ L}`. -/
def countingFunction [LE α] [DecidableLE α] (lam : Nat → α) (L : α) : Nat → Nat
  | 0 => 0
  | K + 1 => countingFunction lam L K + (if lam K ≤ L then 1 else 0)

/-- Discreteness of the spectrum: below every threshold only finitely many eigenvalues occur,
i.e. beyond some index all eigenvalues exceed the threshold. -/
def DiscreteSpectrum [LE α] (lam : Nat → α) : Prop :=
  ∀ L : α, ∃ K : Nat, ∀ n : Nat, K ≤ n → ¬ (lam n ≤ L)

/-- Rayleigh variational monotonicity (RVM): the eigenvalues are enumerated in nondecreasing
order, as produced by the Rayleigh–Ritz min–max variational principle. -/
def RayleighVariationalMonotone [LE α] (lam : Nat → α) : Prop :=
  ∀ i j : Nat, i ≤ j → lam i ≤ lam j

/-- `m` is *the* value of the Weyl counting function at the threshold `L`: the truncated
counts `countingFunction lam L K` are eventually equal to `m`. -/
def IsCountingValue [LE α] [DecidableLE α] (lam : Nat → α) (L : α) (m : Nat) : Prop :=
  ∃ K : Nat, ∀ K' : Nat, K ≤ K' → countingFunction lam L K' = m

section Basic

variable [LE α] [DecidableLE α] {lam : Nat → α} {L : α}

/-- The truncated counting function is monotone in the truncation parameter. -/
theorem countingFunction_mono (K K' : Nat) (h : K ≤ K') :
    countingFunction lam L K ≤ countingFunction lam L K' := by
  induction K' with
  | zero => simp [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_ge n K with hn | hn
    · have : K = n + 1 := Nat.le_antisymm h hn
      subst this
      exact Nat.le_refl _
    · exact Nat.le_trans (ih hn) (Nat.le_add_right _ _)

/-- If all the first `K` eigenvalues lie below the threshold, the truncated count is `K`. -/
theorem countingFunction_eq_self (K : Nat) (h : ∀ n : Nat, n < K → lam n ≤ L) :
    countingFunction lam L K = K := by
  induction K with
  | zero => rfl
  | succ n ih =>
    have hn : lam n ≤ L := h n (Nat.lt_succ_self n)
    have : countingFunction lam L n = n := ih fun m hm => h m (Nat.lt_succ_of_lt hm)
    simp [countingFunction, this, hn]

/-- Beyond a truncation level past which no eigenvalue lies below the threshold, the truncated
counts no longer change. -/
theorem countingFunction_stable {K₀ : Nat} (hK₀ : ∀ n : Nat, K₀ ≤ n → ¬ (lam n ≤ L))
    (K K' : Nat) (hK : K₀ ≤ K) (hKK' : K ≤ K') :
    countingFunction lam L K' = countingFunction lam L K := by
  induction K' with
  | zero =>
    have : K = 0 := Nat.le_zero.mp hKK'
    simp [this]
  | succ n ih =>
    rcases Nat.lt_or_ge n K with hn | hn
    · have : K = n + 1 := Nat.le_antisymm hKK' hn
      subst this
      rfl
    · have hlam : ¬ (lam n ≤ L) := hK₀ n (Nat.le_trans hK hn)
      simp [countingFunction, hlam, ih hn]

end Basic

/-- **Divergence of the Weyl counting function.**

Let `lam : ℕ → α` enumerate the eigenvalues of an operator, with values in a type `α` carrying
a transitive order relation.  Assume:

* `hdisc` — the spectrum is *discrete*: below any threshold only finitely many eigenvalues occur;
* `hrvm` — the eigenvalues are enumerated in nondecreasing order, as delivered by the
  Rayleigh variational (min–max) characterisation.

Then, above every threshold, the counting function `N(L) = #{n | lam n ≤ L}` is well defined
(the truncated counts stabilise) and it diverges: for every `M` there is a threshold `L₀` such
that `N(L) ≥ M` for all `L ≥ L₀`. -/
theorem counting_diverges_of_discrete_and_rvm [LE α] [DecidableLE α]
    (htrans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c) (lam : Nat → α)
    (hdisc : DiscreteSpectrum lam) (hrvm : RayleighVariationalMonotone lam) :
    ∀ M : Nat, ∃ L₀ : α, ∀ L : α, L₀ ≤ L → ∃ m : Nat, IsCountingValue lam L m ∧ M ≤ m := by
  intro M
  refine ⟨lam M, fun L hL => ?_⟩
  obtain ⟨K₀, hK₀⟩ := hdisc L
  refine ⟨countingFunction lam L (max K₀ (M + 1)), ⟨max K₀ (M + 1), fun K' hK' => ?_⟩, ?_⟩
  · exact countingFunction_stable hK₀ _ _ (Nat.le_max_left _ _) hK'
  · have hall : ∀ n : Nat, n < M + 1 → lam n ≤ L := fun n hn =>
      htrans (lam n) (lam M) L (hrvm n M (Nat.lt_succ_iff.mp hn)) hL
    have hM : countingFunction lam L (M + 1) = M + 1 := countingFunction_eq_self (M + 1) hall
    have := countingFunction_mono (lam := lam) (L := L) (M + 1) (max K₀ (M + 1))
      (Nat.le_max_right _ _)
    omega

end Brockian.Weyl.WeylLawTarget

import Mathlib
import Brockian.Weyl.WeylLawTarget

/-!
# The real-valued form of the Weyl counting divergence

`Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm` is stated for an abstract
ordered value type and a truncated counting function (so that the target module itself needs no
imports).  Here we specialise to a real eigenvalue sequence and identify the truncated counting
function with the cardinality `#{n | lam n ≤ Λ}`, obtaining the usual statement that the Weyl
counting function tends to `+∞`.
-/

namespace Brockian.Weyl.WeylLawReal

open Brockian.Weyl.WeylLawTarget

/-- Discreteness of a real spectrum: only finitely many eigenvalues lie below each threshold. -/
def DiscreteSpectrumReal (lam : ℕ → ℝ) : Prop := ∀ Λ : ℝ, {n : ℕ | lam n ≤ Λ}.Finite

/-- The truncated counting function counts exactly the indices `n < K` with `lam n ≤ Λ`. -/
theorem countingFunction_eq_card (lam : ℕ → ℝ) (Λ : ℝ) (K : ℕ) :
    countingFunction lam Λ K = ((Finset.range K).filter (fun n => lam n ≤ Λ)).card := by
  induction K with
  | zero => simp [countingFunction]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : lam n ≤ Λ
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [countingFunction, ih, h]
    · rw [if_neg h]
      simp [countingFunction, ih, h]

/-- Real discreteness implies the abstract discreteness hypothesis of the target theorem. -/
theorem discreteSpectrum_of_real {lam : ℕ → ℝ} (h : DiscreteSpectrumReal lam) :
    DiscreteSpectrum lam := by
  intro Λ
  obtain ⟨K, hK⟩ := (h Λ).bddAbove
  refine ⟨K + 1, fun n hn hcon => ?_⟩
  have : n ≤ K := hK hcon
  omega

/-- Once the truncation level exceeds all indices with `lam n ≤ Λ`, the truncated count equals
the cardinality of the full sublevel set. -/
theorem countingFunction_eq_ncard (lam : ℕ → ℝ) (Λ : ℝ)
    {K : ℕ} (hK : ∀ n : ℕ, K ≤ n → ¬ lam n ≤ Λ) :
    countingFunction lam Λ K = {n : ℕ | lam n ≤ Λ}.ncard := by
  rw [countingFunction_eq_card]
  have hset : {n : ℕ | lam n ≤ Λ} = ↑((Finset.range K).filter (fun n => lam n ≤ Λ)) := by
    ext n
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · intro hn
      exact ⟨by by_contra hc; exact hK n (Nat.le_of_not_lt hc) hn, hn⟩
    · exact fun hn => hn.2
  rw [hset, Set.ncard_coe_finset]

/-- **The Weyl counting function of a discrete spectrum diverges.**
If only finitely many eigenvalues lie below each threshold, then
`N(Λ) = #{n | lam n ≤ Λ} → ∞` as `Λ → ∞`. -/
theorem counting_ncard_tendsto_atTop (lam : ℕ → ℝ) (hdisc : DiscreteSpectrumReal lam)
    (hrvm : RayleighVariationalMonotone lam) :
    Filter.Tendsto (fun Λ : ℝ => {n : ℕ | lam n ≤ Λ}.ncard) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun M => ?_
  obtain ⟨L₀, hL₀⟩ := counting_diverges_of_discrete_and_rvm
    (fun a b c hab hbc => le_trans hab hbc) lam (discreteSpectrum_of_real hdisc) hrvm M
  filter_upwards [Filter.eventually_ge_atTop L₀] with Λ hΛ
  obtain ⟨m, ⟨K, hK⟩, hMm⟩ := hL₀ Λ hΛ
  obtain ⟨K₀, hK₀⟩ := discreteSpectrum_of_real hdisc Λ
  have hcount : countingFunction lam Λ (max K K₀) = m := hK _ (le_max_left _ _)
  have hncard : countingFunction lam Λ (max K K₀) = {n : ℕ | lam n ≤ Λ}.ncard :=
    countingFunction_eq_ncard lam Λ (fun n hn => hK₀ n (le_trans (le_max_right K K₀) hn))
  omega

/-- Sanity check: the hypotheses are satisfiable, e.g. by the spectrum `lam n = n`. -/
example : Filter.Tendsto (fun Λ : ℝ => {n : ℕ | (n : ℝ) ≤ Λ}.ncard) Filter.atTop Filter.atTop := by
  refine counting_ncard_tendsto_atTop (fun n => (n : ℝ)) (fun Λ => ?_) (fun i j hij => ?_)
  · refine Set.Finite.subset (Set.finite_Iic ⌈Λ⌉₊) fun n hn => ?_
    have hn' : (n : ℝ) ≤ Λ := hn
    exact Set.mem_Iic.2 (Nat.cast_le.1 (hn'.trans (Nat.le_ceil Λ)))
  · show ((i : ℝ)) ≤ (j : ℝ)
    exact_mod_cast hij

end Brockian.Weyl.WeylLawReal

