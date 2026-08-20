import Mathlib

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

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first
commands in a file, so the module doc comment above appears immediately after
the single `import Mathlib` line.

Landau's fourth problem ("are there infinitely many primes of the form
`n ^ 2 + 1`?") is an open problem, so what is proved here is a *conditional
reduction*: Bunyakovsky's conjecture implies Landau's fourth conjecture.
The reduction is complete and unconditional in itself: it verifies the two
hypotheses of Bunyakovsky's conjecture for the polynomial `X ^ 2 + 1`
(irreducibility over `ℤ`, and the absence of a fixed prime divisor).

Two unconditional companion results are also proved:
* every prime `p` with `p % 4 ≠ 3` divides some `n ^ 2 + 1`;
* infinitely many primes divide some number of the form `n ^ 2 + 1`.

Mathlib results used: `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`
(irreducibility of `X ^ 2 + 1` over `ℤ`), `ZMod.exists_sq_eq_neg_one_iff`
(`-1` is a square mod `p` iff `p % 4 ≠ 3`) and `Nat.infinite_setOf_prime_modEq_one`
(Dirichlet, primes `≡ 1 [MOD 4]`). No Mathlib lemma settles Landau's fourth problem
itself; it is open.
-/

namespace Brockian.LandauNSquaredPlusOne

open Polynomial

/-- **Bunyakovsky's conjecture**: an integer polynomial `f` with positive leading
coefficient, of degree at least one, irreducible over `ℤ`, and with no fixed prime
divisor (for every prime `p` there is some `n` with `p ∤ f n`) takes prime values
infinitely often. -/
def BunyakovskyConjecture : Prop :=
  ∀ f : Polynomial ℤ, 0 < f.leadingCoeff → 1 ≤ f.natDegree → Irreducible f →
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ¬ ((p : ℤ) ∣ f.eval (n : ℤ))) →
    {n : ℕ | Prime (f.eval (n : ℤ))}.Infinite

section Quadratic

/-- The polynomial `X ^ 2 + 1` over `ℤ`. -/
noncomputable def sqAddOne : Polynomial ℤ := X ^ 2 + C 1

lemma sqAddOne_eq : sqAddOne = X ^ 2 + 1 := by
  simp [sqAddOne]

lemma sqAddOne_monic : sqAddOne.Monic :=
  monic_X_pow_add_C 1 (by norm_num)

lemma sqAddOne_natDegree : sqAddOne.natDegree = 2 := by
  rw [sqAddOne_eq]
  compute_degree!

lemma sqAddOne_eval (n : ℤ) : sqAddOne.eval n = n ^ 2 + 1 := by
  simp [sqAddOne]

lemma sqAddOne_leadingCoeff : 0 < sqAddOne.leadingCoeff := by
  rw [sqAddOne_monic.leadingCoeff]; norm_num

lemma sqAddOne_roots : sqAddOne.roots = 0 := by
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro x hx
  have hx0 : sqAddOne.eval x = 0 := (mem_roots sqAddOne_monic.ne_zero).1 hx
  rw [sqAddOne_eval] at hx0
  nlinarith [sq_nonneg x]

/-- `X ^ 2 + 1` is irreducible over `ℤ`. -/
lemma sqAddOne_irreducible : Irreducible sqAddOne := by
  refine (sqAddOne_monic.irreducible_iff_roots_eq_zero_of_degree_le_three ?_ ?_).2 sqAddOne_roots
  · rw [sqAddOne_natDegree]
  · rw [sqAddOne_natDegree]; norm_num

/-- `X ^ 2 + 1` has no fixed prime divisor: taking `n = 0` gives the value `1`. -/
lemma sqAddOne_no_fixed_prime_divisor (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ¬ ((p : ℤ) ∣ sqAddOne.eval (n : ℤ)) := by
  refine ⟨0, ?_⟩
  rw [sqAddOne_eval]
  intro h
  have h1 : (p : ℤ) ∣ 1 := by simpa using h
  have : p ∣ 1 := by exact_mod_cast h1
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)

end Quadratic

/-- **Conditional reduction (Landau's fourth problem).**
Bunyakovsky's conjecture implies Landau's fourth conjecture: there are infinitely
many `n : ℕ` such that `n ^ 2 + 1` is prime. -/
theorem LandauFourthConjecture (hB : BunyakovskyConjecture) :
    {n : ℕ | Nat.Prime (n ^ 2 + 1)}.Infinite := by
  have h := hB sqAddOne sqAddOne_leadingCoeff (by rw [sqAddOne_natDegree]; norm_num)
    sqAddOne_irreducible sqAddOne_no_fixed_prime_divisor
  have hset : {n : ℕ | Prime (sqAddOne.eval (n : ℤ))} = {n : ℕ | Nat.Prime (n ^ 2 + 1)} := by
    ext n
    simp only [Set.mem_setOf_eq, sqAddOne_eval]
    rw [Int.prime_iff_natAbs_prime]
    have hn : ((n : ℤ) ^ 2 + 1).natAbs = n ^ 2 + 1 := by
      have hc : ((n : ℤ) ^ 2 + 1) = ((n ^ 2 + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hc, Int.natAbs_natCast]
    rw [hn]
  rwa [hset] at h

/-- Every prime `p` with `p % 4 ≠ 3` divides some number of the form `n ^ 2 + 1`.
(Unconditional.) -/
theorem exists_dvd_sq_add_one_of_prime_mod_four_ne_three
    (p : ℕ) (hp : p.Prime) (h : p % 4 ≠ 3) : ∃ n : ℕ, p ∣ n ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 h
  refine ⟨y.val, ?_⟩
  have hz : ((y.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, sq, ← hy]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 hz

/-- Unconditionally, infinitely many primes divide some number of the form `n ^ 2 + 1`. -/
theorem infinite_primes_dvd_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  have hinf : {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD 4]}.Infinite :=
    Nat.infinite_setOf_prime_modEq_one (k := 4) (by norm_num)
  refine hinf.mono ?_
  rintro p ⟨hp, hmod⟩
  have h4 : p % 4 = 1 := by simpa [Nat.ModEq] using hmod
  exact ⟨hp, exists_dvd_sq_add_one_of_prime_mod_four_ne_three p hp (by omega)⟩

end Brockian.LandauNSquaredPlusOne

