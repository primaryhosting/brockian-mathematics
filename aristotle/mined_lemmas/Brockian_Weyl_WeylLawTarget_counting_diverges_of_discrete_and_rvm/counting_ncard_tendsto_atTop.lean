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

