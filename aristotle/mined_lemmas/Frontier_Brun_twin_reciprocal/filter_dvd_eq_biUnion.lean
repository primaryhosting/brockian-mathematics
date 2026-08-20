import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

lemma filter_dvd_eq_biUnion (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) (N : ℕ) :
    (range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2)) =
      T.powerset.biUnion (fun U => (range N).filter
        (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_powerset]
  constructor
  · rintro ⟨hn, hdvd⟩
    refine ⟨T.filter (· ∣ n), Finset.filter_subset _ _, hn, ?_, ?_⟩
    · exact Finset.prod_primes_dvd n
        (fun p hp => Nat.Prime.prime (hT p (Finset.mem_filter.1 hp).1).1)
        (fun p hp => (Finset.mem_filter.1 hp).2)
    · rw [← Finset.filter_not]
      refine Finset.prod_primes_dvd _
        (fun p hp => Nat.Prime.prime (hT p (Finset.mem_filter.1 hp).1).1) ?_
      intro p hp
      obtain ⟨hpT, hpn⟩ := Finset.mem_filter.1 hp
      rcases (Nat.Prime.dvd_mul (hT p hpT).1).1 (hdvd p hpT) with h | h
      · exact absurd h hpn
      · exact h
  · rintro ⟨U, hUT, hn, h1, h2⟩
    refine ⟨hn, ?_⟩
    intro p hp
    by_cases hpU : p ∈ U
    · exact Dvd.dvd.mul_right (dvd_trans (Finset.dvd_prod_of_mem _ hpU) h1) _
    · have hmem : p ∈ T \ U := Finset.mem_sdiff.2 ⟨hp, hpU⟩
      exact Dvd.dvd.mul_left (dvd_trans (Finset.dvd_prod_of_mem _ hmem) h2) _

/-- The pieces of the above decomposition are pairwise disjoint. -/
