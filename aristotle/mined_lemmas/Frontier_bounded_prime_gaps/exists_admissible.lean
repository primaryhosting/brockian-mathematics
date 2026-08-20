import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- The `n`-th prime gap `p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n`. -/

lemma exists_admissible (k : ℕ) : ∃ H : Finset ℕ, H.card = k ∧ IsAdmissible H := by
  classical
  have hsm : StrictMono (fun i => Nat.nth Nat.Prime (k + i)) := by
    intro a b hab
    exact nth_prime_lt_nth_prime (by omega)
  set H : Finset ℕ := (Finset.range k).image (fun i => Nat.nth Nat.Prime (k + i)) with hHdef
  have hcardH : H.card = k := by
    rw [hHdef, Finset.card_image_of_injective _ hsm.injective, Finset.card_range]
  have hmem : ∀ x ∈ H, k < x ∧ Nat.Prime x := by
    intro x hx
    rw [hHdef, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨?_, Nat.prime_nth_prime _⟩
    have := Nat.add_two_le_nth_prime (k + i)
    omega
  refine ⟨H, hcardH, ?_⟩
  intro p hp
  by_cases hpk : p ≤ k
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨hxk, hxp⟩ := hmem x hx
    have hnd : ¬ p ∣ x := by
      intro hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp hxp).1 hdvd
      omega
    simpa [ZMod.natCast_eq_zero_iff] using hnd
  · push_neg at hpk
    by_contra hcon
    push_neg at hcon
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ Finset.image (fun x : ℕ => (x : ZMod p)) H := by
      intro r _
      obtain ⟨x, hx, hxr⟩ := hcon r
      exact Finset.mem_image.2 ⟨x, hx, hxr⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card p] at hcard
    have hle : (Finset.image (fun x : ℕ => (x : ZMod p)) H).card ≤ k :=
      Finset.card_image_le.trans (le_of_eq hcardH)
    omega

/-- From `DHL[k,2]` one extracts infinitely many pairs of primes at bounded distance. -/
