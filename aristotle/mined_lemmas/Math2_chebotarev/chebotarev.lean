/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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

namespace Math2

open ArithmeticFunction Complex Filter Topology

/-! ### The analytic input: Λ-weighted density of a residue class -/

/-- The terms of the `L`-series of the von Mangoldt function restricted to a residue class,
evaluated at a real point, are real. -/

theorem chebotarev (q : ℕ) [NeZero q]
    (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' n : ℕ,
        {p : ℕ | p.Prime ∧ IsFrobeniusAt q p σ}.indicator
          (fun n : ℕ => vonMangoldt n / (n : ℝ) ^ s) n)
      (𝓝[>] (1 : ℝ))
      (𝓝 ((Nat.card {τ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ | IsConj σ τ} : ℝ)
        / (Nat.card (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) : ℝ))) := by
  obtain ⟨a, ha, hfrob⟩ := exists_residue_isFrobeniusAt q σ
  rw [card_conjClass q σ, card_gal q]
  have hlim := tendsto_primes_density q ha
  simp only [Nat.cast_one, one_div]
  refine hlim.congr fun s => ?_
  congr 1
  refine tsum_congr fun n => ?_
  by_cases hn : n.Prime
  · by_cases hna : (n : ZMod q) = a
    · rw [Set.indicator_of_mem (by exact ⟨hn, (hfrob n).mpr hna⟩)]
      simp [hn, vonMangoldt.residueClass, hna]
    · rw [Set.indicator_of_notMem (by
        simp only [Set.mem_setOf_eq, not_and]
        intro _ hf
        exact hna ((hfrob n).mp hf))]
      simp [hn, vonMangoldt.residueClass, hna]
  · rw [Set.indicator_of_notMem (by
      simp only [Set.mem_setOf_eq, not_and]
      intro h
      exact absurd h hn)]
    simp [hn]

/-- A qualitative consequence of the above: for every element `σ` of the Galois group of
`ℚ(ζ_q)/ℚ` there are infinitely many primes whose Frobenius is `σ`. -/
