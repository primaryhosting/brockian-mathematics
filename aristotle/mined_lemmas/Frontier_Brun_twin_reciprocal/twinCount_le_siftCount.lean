import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma twinCount_le_siftCount (N z : ℕ) : twinCount N ≤ (z + 1) + siftCount N z := by
  have hsub : (range N).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))
      ⊆ (range (z + 1)) ∪ ((range N).filter (fun n => ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2))) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hn1, hn2⟩ := hn
    rw [Finset.mem_union]
    by_cases hz : n ≤ z
    · left; simp only [Finset.mem_range]; omega
    · right
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hnN, fun p hp hdvd => ?_⟩
      obtain ⟨hple, hpp, _⟩ := mem_oddPrimesLe.mp hp
      rcases hpp.dvd_mul.mp hdvd with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hpp hn1).mp h
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hpp hn2).mp h
        omega
  calc twinCount N ≤ ((range (z + 1)) ∪ ((range N).filter
        (fun n => ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2)))).card := Finset.card_le_card hsub
    _ ≤ (range (z + 1)).card + ((range N).filter
        (fun n => ∀ p ∈ oddPrimesLe z, ¬ p ∣ n * (n + 2))).card := Finset.card_union_le _ _
    _ = (z + 1) + siftCount N z := by rw [Finset.card_range]; rfl

