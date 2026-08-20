import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

lemma artinPrimes_subset_of_isSquare {a : ℤ} (ha : IsSquare a) :
    artinPrimes a ⊆ {2} := by
  rintro p ⟨hp, hprim⟩
  by_contra hne
  simp only [Set.mem_singleton_iff] at hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hne
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨b, hb⟩ := ha
  have hab : (a : ZMod p) = (b : ZMod p) * (b : ZMod p) := by
    rw [hb]; push_cast; ring
  have hbne : (b : ZMod p) ≠ 0 := by
    intro h0
    exact ne_zero_of_isPrimitiveRootMod hp hprim (by rw [hab, h0, mul_zero])
  have hhalf : ((a : ZMod p)) ^ ((p - 1) / 2) = 1 := by
    have h2 : 2 * ((p - 1) / 2) = p - 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rw [hab, ← sq, ← pow_mul, h2]
    exact ZMod.pow_card_sub_one_eq_one hbne
  have hdvd : orderOf ((a : ZMod p)) ∣ (p - 1) / 2 := orderOf_dvd_of_pow_eq_one hhalf
  rw [hprim] at hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

