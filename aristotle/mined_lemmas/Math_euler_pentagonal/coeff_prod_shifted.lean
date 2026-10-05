import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-! ## Distinct partitions as finsets of positive integers -/

/-- The finset of all "partitions of `n` into distinct parts", encoded as finsets of
positive integers whose sum is `n`. -/

lemma coeff_prod_shifted (T : Finset ℕ) (n : ℕ) (h0 : 0 ∉ T) (hsub : Finset.Icc 1 n ⊆ T) :
    (PowerSeries.coeff n) (∏ j ∈ T, (1 - (X : ℤ⟦X⟧) ^ j))
      = ∑ S ∈ distinctSets n, ((-1 : ℤ)) ^ S.card := by
  have hexp : (∏ j ∈ T, (1 - (X : ℤ⟦X⟧) ^ j))
      = ∑ t ∈ T.powerset, ((-1 : ℤ⟦X⟧)) ^ t.card * X ^ (∑ i ∈ t, i) := by
    have h := Finset.prod_add (fun j => -((X : ℤ⟦X⟧) ^ j)) (fun _ => (1 : ℤ⟦X⟧)) T
    simp only [Finset.prod_const_one, mul_one] at h
    rw [show (∏ j ∈ T, (1 - (X : ℤ⟦X⟧) ^ j)) = ∏ j ∈ T, (-((X : ℤ⟦X⟧) ^ j) + 1) from
      Finset.prod_congr rfl (fun j _ => by ring), h]
    exact Finset.sum_congr rfl (fun t _ => by rw [Finset.prod_neg, Finset.prod_pow_eq_pow_sum])
  have hcoeff : ∀ k m : ℕ, (PowerSeries.coeff (R := ℤ) n) (((-1 : ℤ⟦X⟧)) ^ k * X ^ m)
      = if m = n then ((-1 : ℤ)) ^ k else 0 := by
    intro k m
    rw [show ((-1 : ℤ⟦X⟧)) ^ k = C ((-1 : ℤ) ^ k) by rw [map_pow]; norm_num,
      PowerSeries.coeff_C_mul]
    rcases eq_or_ne m n with rfl | h
    · simp
    · rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm h), if_neg h]; ring
  rw [hexp, map_sum]
  simp only [hcoeff]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun t _ => rfl)
  ext t
  simp only [distinctSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hT, hsum⟩
    refine ⟨fun x hx => ?_, hsum⟩
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hT hx)
    have hxn : x ≤ n := hsum ▸ Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    simp only [Finset.mem_Icc]
    omega
  · rintro ⟨hT, hsum⟩
    exact ⟨fun x hx => hsub (hT hx), hsum⟩

