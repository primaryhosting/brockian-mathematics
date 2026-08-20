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
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

lemma twinCount_le_sifted (x z : ℕ) :
    (twinCount x : ℝ) ≤ (z + 1) + (twinSieve x z).siftedSum := by
  rw [siftedSum_twinSieve]
  have hsub : (range (x + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime) ⊆
      (range (z + 1)) ∪ ((Finset.Icc 1 x).filter
        (fun n => Nat.Coprime (bigP z) (n * (n + 2)))) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, hpp, hpp2⟩ := hp
    rcases le_or_gt p z with h | h
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpp.pos, by omega⟩, ?_⟩)
      rw [bigP]
      refine Nat.Coprime.prod_left (fun q hq => ?_)
      have hqp : q.Prime := prime_of_mem_oddPrimesBelow hq
      have hqz : q ≤ z := (mem_oddPrimesBelow.mp hq).2.2
      rw [Nat.Prime.coprime_iff_not_dvd hqp]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hqp).mp hdvd with h1 | h1
      · have := (Nat.prime_dvd_prime_iff_eq hqp hpp).mp h1; omega
      · have := (Nat.prime_dvd_prime_iff_eq hqp hpp2).mp h1; omega
  have hcard := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (range (z + 1))
    ((Finset.Icc 1 x).filter (fun n => Nat.Coprime (bigP z) (n * (n + 2))))
  rw [twinCount]
  have : ((range (x + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)).card ≤
      (z + 1) + ((Finset.Icc 1 x).filter (fun n => Nat.Coprime (bigP z) (n * (n + 2)))).card := by
    simpa using hcard.trans h2
  exact_mod_cast this

