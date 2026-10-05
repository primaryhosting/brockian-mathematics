/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
two distinct positive integers each of whose sum of divisors equals `m + n + 1`;
equivalently, the sum of the proper divisors of each member is the other member plus one. -/

lemma eq_nine_of_sigma_rel {u : ℕ} (hupos : 0 < u) (key : 3 * σ 1 u = 4 * u + 3) : u = 9 := by
  have hsig3 : σ 1 3 = 4 := by rw [sigma_one_apply]; decide
  have h3u : 3 ∣ u :=
    Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) (⟨σ 1 u - 1, by omega⟩ : (3 : ℕ) ∣ 4 * u)
  obtain ⟨d, hd⟩ := h3u
  have hu3 : 3 < u := by
    rcases Nat.lt_or_ge u 4 with h | h
    · have hu' : u = 3 := by omega
      rw [hu', hsig3] at key
      omega
    · exact h
  have hune : u ≠ 0 := by omega
  have hdne1 : d ≠ 1 := by omega
  have hdneu : d ≠ u := by omega
  have h1neu : (1 : ℕ) ≠ u := by omega
  have hT : ({1, d, u} : Finset ℕ) ⊆ u.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd u, hune⟩
    · exact Nat.mem_divisors.mpr ⟨⟨3, by omega⟩, hune⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hune⟩
  have hsumT : ∑ x ∈ ({1, d, u} : Finset ℕ), x = 1 + d + u := by
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨fun h => hdne1 h.symm, h1neu⟩),
      Finset.sum_insert (by simpa using hdneu), Finset.sum_singleton]
    omega
  have h3mem : (3 : ℕ) ∈ ({1, d, u} : Finset ℕ) := by
    by_contra hc
    have hlt : ∑ x ∈ ({1, d, u} : Finset ℕ), x < ∑ x ∈ u.divisors, x :=
      Finset.sum_lt_sum_of_subset hT (Nat.mem_divisors.mpr ⟨⟨d, by omega⟩, hune⟩) hc
        (by norm_num) (fun j _ _ => Nat.zero_le j)
    rw [hsumT, ← sigma_one_apply] at hlt
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at h3mem
  omega

/-- The base `2` is impossible: `2 ^ a` is never a member of a betrothed pair. -/
