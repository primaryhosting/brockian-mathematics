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

/-
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 rejects a module doc comment `/-! ... -/` before `import`, so the header above
-- is an ordinary block comment; its text is otherwise exactly as requested.)

import Mathlib

/-!
# Landau's fourth problem: infinitely many primes of the form `n ^ 2 + 1`

Landau's fourth conjecture is an open problem.  This file provides:

* a formal statement of Bunyakovsky's conjecture (`Bunyakovsky`);
* a Lean-checked *conditional reduction*: Landau's fourth conjecture follows from
  Bunyakovsky's conjecture (`LandauFourthConjecture`), via the irreducibility of
  `X ^ 2 + 1` over `ℤ` and the absence of a fixed divisor;
* unconditional partial results: an odd prime divides some `n ^ 2 + 1` iff it is
  `1 mod 4`, and hence infinitely many primes divide numbers of the form `n ^ 2 + 1`.
-/

namespace Brockian.LandauNSquaredPlusOne

open Polynomial

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime. -/
def LandauSet : Set ℕ := {n : ℕ | Nat.Prime (n ^ 2 + 1)}

/-- **Bunyakovsky's conjecture**: an integer polynomial `f` of positive degree with positive
leading coefficient, irreducible over `ℤ`, and with no fixed divisor `d > 1`,
takes prime values at arbitrarily large integers. -/
def Bunyakovsky : Prop :=
  ∀ f : Polynomial ℤ, 0 < f.natDegree → Irreducible f → 0 < f.leadingCoeff →
    (∀ d : ℤ, 1 < d → ∃ n : ℤ, ¬ (d ∣ f.eval n)) →
    ∀ N : ℤ, ∃ n : ℤ, N < n ∧ Prime (f.eval n)

theorem monic_X_sq_add_one : (X ^ 2 + 1 : ℤ[X]).Monic := by
  monicity!

theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by
  compute_degree!

/-- `X ^ 2 + 1` is irreducible over `ℤ`, since it is monic and irreducible mod `3`. -/
theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℤ[X]) := by
  refine Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3)) _
    monic_X_sq_add_one ?_
  have hmap : ((X ^ 2 + 1 : ℤ[X]).map (Int.castRingHom (ZMod 3))) = (X ^ 2 + 1 : (ZMod 3)[X]) := by
    simp
  rw [hmap]
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have h : (X ^ 2 + 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
    simp [h]
  · intro x hx
    rw [Polynomial.IsRoot.def] at hx
    simp only [eval_add, eval_pow, eval_X, eval_one] at hx
    revert hx
    revert x
    decide

/-- `X ^ 2 + 1` has no fixed divisor `d > 1`: already `0 ^ 2 + 1 = 1`. -/
theorem no_fixed_divisor_X_sq_add_one :
    ∀ d : ℤ, 1 < d → ∃ n : ℤ, ¬ (d ∣ (X ^ 2 + 1 : ℤ[X]).eval n) := by
  intro d hd
  refine ⟨0, ?_⟩
  simp only [eval_add, eval_pow, eval_X, eval_one]
  intro h
  have := Int.le_of_dvd (by norm_num) h
  omega

/-- **Landau's fourth conjecture**, conditionally on Bunyakovsky's conjecture: there are
infinitely many natural numbers `n` such that `n ^ 2 + 1` is prime. -/
theorem LandauFourthConjecture (hB : Bunyakovsky) : LandauSet.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hprime⟩ :=
    hB (X ^ 2 + 1) (by rw [natDegree_X_sq_add_one]; norm_num) irreducible_X_sq_add_one
      (by rw [monic_X_sq_add_one.leadingCoeff]; norm_num) no_fixed_divisor_X_sq_add_one (a : ℤ)
  have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg a) hn.le
  lift n to ℕ using hn0 with m
  have hev : (X ^ 2 + 1 : ℤ[X]).eval (m : ℤ) = ((m ^ 2 + 1 : ℕ) : ℤ) := by push_cast; simp
  rw [hev] at hprime
  refine ⟨m, ?_, by exact_mod_cast hn⟩
  have : Nat.Prime (m ^ 2 + 1) := by simpa using Int.prime_iff_natAbs_prime.mp hprime
  exact this

/-- Restatement of the conditional result: assuming Bunyakovsky's conjecture, for every `N`
there is some `n > N` with `n ^ 2 + 1` prime. -/
theorem exists_gt_prime_sq_add_one (hB : Bunyakovsky) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Nat.Prime (n ^ 2 + 1) := by
  obtain ⟨n, hn, hlt⟩ := (LandauFourthConjecture hB).exists_gt N
  exact ⟨n, hlt, hn⟩

/-! ## Unconditional partial results -/

/-- For an odd prime `p`, `p` divides some number of the form `n ^ 2 + 1` if and only if
`p ≡ 1 [MOD 4]`. -/
theorem prime_dvd_sq_add_one_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ n : ℕ, p ∣ n ^ 2 + 1) ↔ p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  constructor
  · rintro ⟨n, hn⟩
    have h : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hn
    push_cast at h
    have hsq : IsSquare (-1 : ZMod p) := ⟨(n : ZMod p), by linear_combination -h⟩
    have := (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 hsq
    omega
  · intro h4
    obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 (by omega)
    refine ⟨y.val, ?_⟩
    have h : ((y.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
      linear_combination -hy
    exact (ZMod.natCast_eq_zero_iff _ _).1 h

/-- Unconditionally, infinitely many primes divide some number of the form `n ^ 2 + 1`. -/
theorem infinite_setOf_prime_dvd_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hp, hap, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 4) (max a 2) (by norm_num)
  have h4 : p % 4 = 1 := by
    unfold Nat.ModEq at hmod
    omega
  exact ⟨p, ⟨hp, (prime_dvd_sq_add_one_iff hp (by omega)).2 h4⟩, by omega⟩

end Brockian.LandauNSquaredPlusOne

