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
