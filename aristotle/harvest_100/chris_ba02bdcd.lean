import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The wheel modulus of this instance. -/
def wheelModulus1051 : ℕ := 1051

lemma prime_wheelModulus1051 : Nat.Prime wheelModulus1051 := by
  unfold wheelModulus1051
  norm_num

/-- Every nonzero residue below the (prime) wheel modulus is coprime to it. -/
lemma coprime_wheelModulus1051 {k : ℕ} (hk : 0 < k) (hlt : k < wheelModulus1051) :
    Nat.Coprime k wheelModulus1051 := by
  have h : Nat.Coprime wheelModulus1051 k :=
    (Nat.Prime.coprime_iff_not_dvd prime_wheelModulus1051).2
      (Nat.not_dvd_of_pos_of_lt hk hlt)
  exact h.symm

/-- **Wheel decomposition of a residue.** Every residue class modulo the wheel modulus
`1051` is the sum of two residues that are invertible on the wheel (i.e. coprime to the
modulus). This is the combinatorial heart of the statement: it says the `K = 2` wheel
covers all of `ZMod 1051`. -/
lemma exists_wheel_pair (n : ℕ) :
    ∃ a b : ℕ, Nat.Coprime a wheelModulus1051 ∧ Nat.Coprime b wheelModulus1051 ∧
      a + b ≡ n [MOD wheelModulus1051] := by
  have hmod : n % wheelModulus1051 ≡ n [MOD wheelModulus1051] := Nat.mod_modEq n _
  have hlt : n % wheelModulus1051 < wheelModulus1051 :=
    Nat.mod_lt _ (by unfold wheelModulus1051; norm_num)
  set r := n % wheelModulus1051 with hr
  rcases Nat.lt_or_ge r 2 with h2 | h2
  · interval_cases r
    · -- r = 0 : use 1 + 1050 = 1051 ≡ 0
      refine ⟨1, 1050, coprime_wheelModulus1051 (by norm_num) (by unfold wheelModulus1051; norm_num),
        coprime_wheelModulus1051 (by norm_num) (by unfold wheelModulus1051; norm_num), ?_⟩
      refine Nat.ModEq.trans ?_ hmod
      show (1051 : ℕ) ≡ 0 [MOD wheelModulus1051]
      unfold wheelModulus1051
      decide
    · -- r = 1 : use 2 + 1050 = 1052 ≡ 1
      refine ⟨2, 1050, coprime_wheelModulus1051 (by norm_num) (by unfold wheelModulus1051; norm_num),
        coprime_wheelModulus1051 (by norm_num) (by unfold wheelModulus1051; norm_num), ?_⟩
      refine Nat.ModEq.trans ?_ hmod
      show (1052 : ℕ) ≡ 1 [MOD wheelModulus1051]
      unfold wheelModulus1051
      decide
  · -- r ≥ 2 : use 1 + (r - 1) = r
    refine ⟨1, r - 1, coprime_wheelModulus1051 (by norm_num) (by unfold wheelModulus1051; norm_num),
      coprime_wheelModulus1051 (by omega) (by omega), ?_⟩
    have : 1 + (r - 1) = r := by omega
    rw [this]
    exact hmod

/-- **Goldbach wheel of order `K = 2` for the modulus `1051`.**

For every target `n` and every bound `N`, there are two primes `p, q > N` whose sum lies in
the residue class of `n` modulo `1051`. Equivalently (contrapositive form): no residue class
modulo the wheel modulus `1051` can avoid being hit by sums of two arbitrarily large primes.

The proof combines the wheel decomposition `exists_wheel_pair` (every residue mod `1051`
splits as a sum of two units of the wheel, using that `1051` is prime) with Dirichlet's
theorem on primes in arithmetic progressions. -/
theorem GoldbachWheelK2_1051 (n N : ℕ) :
    ∃ p q : ℕ, N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧
      p + q ≡ n [MOD wheelModulus1051] := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_wheel_pair n
  have hq0 : wheelModulus1051 ≠ 0 := by unfold wheelModulus1051; norm_num
  obtain ⟨p, hpN, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_modEq N hq0 ha
  obtain ⟨q, hqN, hq, hqb⟩ := Nat.forall_exists_prime_gt_and_modEq N hq0 hb
  exact ⟨p, q, hpN, hqN, hp, hq, (hpa.add hqb).trans hab⟩

/-- `ZMod`-form of the wheel statement: sums of two primes exceeding any prescribed bound
cover all of `ZMod 1051`. -/
theorem GoldbachWheelK2_1051_zmod (x : ZMod wheelModulus1051) (N : ℕ) :
    ∃ p q : ℕ, N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧
      ((p : ZMod wheelModulus1051) + (q : ZMod wheelModulus1051)) = x := by
  obtain ⟨p, q, hpN, hqN, hp, hq, h⟩ := GoldbachWheelK2_1051 x.val N
  refine ⟨p, q, hpN, hqN, hp, hq, ?_⟩
  have hcast : ((p + q : ℕ) : ZMod wheelModulus1051) = ((x.val : ℕ) : ZMod wheelModulus1051) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have : NeZero wheelModulus1051 := ⟨by unfold wheelModulus1051; norm_num⟩
  simpa using hcast

end Brockian

