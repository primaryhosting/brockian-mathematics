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

lemma exists_good_subset (R : Finset ℕ) (hR : ∀ p ∈ R, 3 ≤ p) (T : ℝ) (hT : 0 ≤ T)
    (hbig : T ≤ ∑ p ∈ R, 2/(p:ℝ)) :
    ∃ Q ⊆ R, T ≤ ∑ p ∈ Q, 2/(p:ℝ) ∧ ∑ p ∈ Q, 2/(p:ℝ) ≤ T + 1 := by
  classical
  set F := R.powerset.filter (fun Q : Finset ℕ => T ≤ ∑ p ∈ Q, 2/(p:ℝ)) with hF
  have hRF : R ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl R, hbig⟩
  obtain ⟨Q, hQF, hQmin⟩ := Finset.exists_min_image F Finset.card ⟨R, hRF⟩
  rw [hF, Finset.mem_filter, Finset.mem_powerset] at hQF
  refine ⟨Q, hQF.1, hQF.2, ?_⟩
  by_contra hc
  push_neg at hc
  have hQne : Q.Nonempty := by
    rcases Finset.eq_empty_or_nonempty Q with h | h
    · rw [h] at hc
      simp at hc
      linarith
    · exact h
  obtain ⟨p, hp⟩ := hQne
  have hp3 : (3:ℝ) ≤ p := by exact_mod_cast hR p (hQF.1 hp)
  have herase : ∑ q ∈ Q.erase p, 2/(q:ℝ) = (∑ q ∈ Q, 2/(q:ℝ)) - 2/(p:ℝ) := by
    have := Finset.add_sum_erase Q (fun q => 2/(q:ℝ)) hp
    linarith [this]
  have hple : 2/(p:ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hmem : Q.erase p ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨(Finset.erase_subset _ _).trans hQF.1, ?_⟩
    rw [herase]
    linarith
  have := hQmin _ hmem
  have hcard := Finset.card_erase_of_mem hp
  have : 0 < Q.card := Finset.card_pos.2 ⟨p, hp⟩
  omega

/-- The exponent appearing in the error term of the sieve, for parameter `j`. -/
