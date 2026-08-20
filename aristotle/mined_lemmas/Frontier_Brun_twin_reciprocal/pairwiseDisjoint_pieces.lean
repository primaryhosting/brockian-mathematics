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

lemma pairwiseDisjoint_pieces (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) (N : ℕ) :
    ((T.powerset : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint
      (fun U => (range N).filter (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) := by
  classical
  have key : ∀ U V : Finset ℕ, U ⊆ T → V ⊆ T → (∃ p, p ∈ U ∧ p ∉ V) →
      Disjoint ((range N).filter (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2))
        ((range N).filter (fun n => (∏ p ∈ V, p) ∣ n ∧ (∏ p ∈ T \ V, p) ∣ n+2)) := by
    intro U V hU hV ⟨p, hpU, hpV⟩
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_filter] at hn1 hn2
    have hpT : p ∈ T := hU hpU
    have hpn : p ∣ n := dvd_trans (Finset.dvd_prod_of_mem _ hpU) hn1.2.1
    have hpn2 : p ∣ n + 2 :=
      dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_sdiff.2 ⟨hpT, hpV⟩)) hn2.2.2
    have hd2 : p ∣ 2 := (Nat.dvd_add_right hpn).1 hpn2
    exact (hT p hpT).2 ((Nat.prime_dvd_prime_iff_eq (hT p hpT).1 Nat.prime_two).1 hd2)
  intro U hU V hV hUV
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset] at hU hV
  by_cases h : ∃ p, p ∈ U ∧ p ∉ V
  · exact key U V hU hV h
  · push_neg at h
    have h2 : ∃ p, p ∈ V ∧ p ∉ U := by
      by_contra hc
      push_neg at hc
      exact hUV (Finset.Subset.antisymm h hc)
    exact (key V U hV hU h2).symm

/-- Each piece of the decomposition has cardinality within `1` of `N / ∏ p ∈ T, p`. -/
