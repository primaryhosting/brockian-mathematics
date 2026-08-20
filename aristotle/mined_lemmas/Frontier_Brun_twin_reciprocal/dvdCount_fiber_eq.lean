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

lemma dvdCount_fiber_eq (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2)
    {T : Finset ℕ} (hT : T ⊆ S) :
    ((range N).filter (fun n => ∀ p ∈ S, p ∣ n * (n + 2))).filter
        (fun n => S.filter (fun p => p ∣ n) = T)
      = (range N).filter (fun n => (∏ p ∈ T, p) ∣ n ∧ (∏ p ∈ S \ T, p) ∣ (n + 2)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hn, hdvd⟩, hfib⟩
    refine ⟨hn, ?_, ?_⟩
    · refine Finset.prod_primes_dvd n (fun p hp => (hS p (hT hp)).1.prime) (fun p hp => ?_)
      have : p ∈ S.filter (fun p => p ∣ n) := by rw [hfib]; exact hp
      exact (Finset.mem_filter.mp this).2
    · refine Finset.prod_primes_dvd (n + 2) (fun p hp => (hS p (Finset.mem_sdiff.mp hp).1).1.prime)
        (fun p hp => ?_)
      obtain ⟨hpS, hpT⟩ := Finset.mem_sdiff.mp hp
      have hpn : ¬ p ∣ n := by
        intro h
        exact hpT (by rw [← hfib]; exact Finset.mem_filter.mpr ⟨hpS, h⟩)
      have := (hS p hpS).1.dvd_mul.mp (hdvd p hpS)
      tauto
  · rintro ⟨hn, hT1, hT2⟩
    have hdvd : ∀ p ∈ S, p ∣ n * (n + 2) := by
      intro p hp
      by_cases hpT : p ∈ T
      · exact Dvd.dvd.mul_right (dvd_trans (Finset.dvd_prod_of_mem _ hpT) hT1) _
      · have : p ∈ S \ T := Finset.mem_sdiff.mpr ⟨hp, hpT⟩
        exact Dvd.dvd.mul_left (dvd_trans (Finset.dvd_prod_of_mem _ this) hT2) _
    refine ⟨⟨hn, hdvd⟩, ?_⟩
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpS, hpn⟩
      by_contra hpT
      have hmem : p ∈ S \ T := Finset.mem_sdiff.mpr ⟨hpS, hpT⟩
      have hp2 : p ∣ n + 2 := dvd_trans (Finset.dvd_prod_of_mem _ hmem) hT2
      have hdvd2 : p ∣ 2 := (Nat.dvd_add_iff_right hpn).mpr hp2
      have h1 := (hS p hpS).1.two_le
      have h2 := (hS p hpS).2
      have := Nat.le_of_dvd (by norm_num) hdvd2
      omega
    · intro hpT
      exact ⟨hT hpT, dvd_trans (Finset.dvd_prod_of_mem _ hpT) hT1⟩

/-- If each of finitely many quantities is within `1` of `c`, their sum is within `#s` of
`#s * c`. -/
