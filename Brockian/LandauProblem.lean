import Mathlib

/-!
# LandauProblem

Partial results toward **Landau's fourth problem** (`n^2 + 1` prime infinitely often).  **OPEN** — recorded below as an unproven `def`, never a theorem.

Tier A (this file, now): the open statement as an unproven `def`.
Tier B (appended as proofs land): genuine unconditional partial results.
-/

namespace Brockian.LandauProblem

/-- Landau's fourth problem (**OPEN**), recorded as an unproven `def`:
infinitely many `n` have `n ^ 2 + 1` prime. -/
def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

theorem even_of_sq_add_one_prime {n : ℕ} (hn : 1 < n)
    (h : (n ^ 2 + 1).Prime) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exfalso
    have h2 : 2 ∣ n ^ 2 + 1 := by
      have : Odd (n ^ 2) := ho.pow
      exact this.add_one.two_dvd
    have := (Nat.Prime.eq_one_or_self_of_dvd h 2 h2)
    have hlt : 2 < n ^ 2 + 1 := by nlinarith
    rcases this with h1 | h1 <;> omega

/-- Every odd prime divisor `p` of `n ^ 2 + 1` satisfies `p % 4 = 1`:
in `ZMod p` the element `n` squares to `-1`, so `-1` is a quadratic residue,
which forces `p % 4 ≠ 3`; oddness then leaves only `p % 4 = 1`. -/
theorem odd_prime_dvd_sq_add_one_mod_four {n p : ℕ}
    (hp : Nat.Prime p) (hodd : Odd p) (h : p ∣ n ^ 2 + 1) :
    p % 4 = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
  push_cast at h0
  have hsq : IsSquare (-1 : ZMod p) := ⟨(n : ZMod p), by linear_combination -h0⟩
  have h3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  omega

/-- Squares are `0` or `1` mod `3`, hence `n ^ 2 + 1` is never divisible by `3`. -/
theorem three_not_dvd_sq_add_one (n : ℕ) : ¬ (3 ∣ n ^ 2 + 1) := by
  intro h
  have hmod : (n ^ 2 + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have hpow : n ^ 2 % 3 = (n % 3) ^ 2 % 3 := Nat.pow_mod n 2 3
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : (n % 3) <;> omega

/-- For `n > 0`, `n ^ 2 + 1` lies strictly between the consecutive squares
`n ^ 2` and `(n + 1) ^ 2`, hence is never a perfect square. -/
theorem not_isSquare_sq_add_one (n : ℕ) (hn : 0 < n) : ¬ IsSquare (n ^ 2 + 1) := by
  rintro ⟨r, hr⟩
  have h1 : n < r := by nlinarith
  have h2 : r < n + 1 := by nlinarith
  omega

/-- Landau's `n ^ 2 + 1` problem is equivalent to its even sub-sequence version:
for odd `n > 1` the number `n ^ 2 + 1` is even and larger than `2`, hence composite,
so the only odd witness is `n = 1`. -/
theorem landau_iff_even_infinite :
    LandauNSqPlusOne ↔ {n : ℕ | Even n ∧ (n ^ 2 + 1).Prime}.Infinite := by
  constructor
  · intro h
    have hsub : {n : ℕ | (n ^ 2 + 1).Prime} ⊆
        {n : ℕ | Even n ∧ (n ^ 2 + 1).Prime} ∪ {1} := by
      intro n hn
      simp only [Set.mem_setOf_eq] at hn
      rcases Nat.even_or_odd n with he | ho
      · exact Or.inl ⟨he, hn⟩
      · right
        obtain ⟨k, hk⟩ := ho
        have h2 : (2 : ℕ) ∣ n ^ 2 + 1 := ⟨2 * k ^ 2 + 2 * k + 1, by subst hk; ring⟩
        have h3 : n ^ 2 + 1 = 2 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hn).mp h2).symm
        have : n = 1 := by nlinarith
        simpa using this
    have hu : ({n : ℕ | Even n ∧ (n ^ 2 + 1).Prime} ∪ {1}).Infinite := h.mono hsub
    by_contra hfin
    exact hu (Set.not_infinite.mp hfin |>.union (Set.finite_singleton 1))
  · intro h
    exact h.mono (fun n hn => hn.2)

/-- `n ^ 2 + 1` is never divisible by `4`: squares are `0` or `1` mod `4`, so
`n ^ 2 + 1` is `1` or `2` mod `4`. -/
theorem four_not_dvd_sq_add_one (n : ℕ) : ¬ (4 ∣ n ^ 2 + 1) := by
  intro h
  have hm : (n ^ 2 + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h
  have h2 : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := Nat.pow_mod n 2 4
  have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hh : (n % 4) <;> omega

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

/-- `n` and `n ^ 2 + 1` are coprime, since `(n ^ 2 + 1) - n * n = 1`. -/
theorem coprime_sq_add_one (n : ℕ) : Nat.Coprime n (n ^ 2 + 1) := by
  simp [Nat.Coprime, pow_two]

/-- For even `n > 1`, the odd number `n ^ 2 + 1` exceeds `1`, so it has an odd prime factor,
and every odd prime factor of `n ^ 2 + 1` is congruent to `1` mod `4` (since `-1` is a square
mod such a prime). -/
theorem exists_prime_mod_four_dvd_sq_add_one {n : ℕ} (hn : 1 < n) (he : Even n) :
    ∃ p, Nat.Prime p ∧ p % 4 = 1 ∧ p ∣ n ^ 2 + 1 := by
  have hm1 : n ^ 2 + 1 ≠ 1 := by nlinarith
  have hpp : (n ^ 2 + 1).minFac.Prime := Nat.minFac_prime hm1
  have hdvd : (n ^ 2 + 1).minFac ∣ n ^ 2 + 1 := Nat.minFac_dvd _
  have hodd : ¬ (2 ∣ n ^ 2 + 1) := by
    obtain ⟨k, hk⟩ := he
    have hsq : n ^ 2 = 2 * (2 * k ^ 2) := by subst hk; ring
    omega
  have hp2 : (n ^ 2 + 1).minFac ≠ 2 := by
    intro h
    rw [h] at hdvd
    exact hodd hdvd
  haveI : Fact (n ^ 2 + 1).minFac.Prime := ⟨hpp⟩
  have hsq : IsSquare (-1 : ZMod (n ^ 2 + 1).minFac) := by
    refine ⟨(n : ZMod (n ^ 2 + 1).minFac), ?_⟩
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (n ^ 2 + 1).minFac) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    linear_combination -h0
  have h4 : (n ^ 2 + 1).minFac % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.1 hsq
  have hodd' : (n ^ 2 + 1).minFac % 2 = 1 := Nat.odd_iff.1 (hpp.odd_of_ne_two hp2)
  exact ⟨_, hpp, by omega, hdvd⟩

/-- Landau's `n² + 1` statement is equivalent to the unbounded-witness form:
for every bound `N` there is some `n > N` with `n² + 1` prime. -/
theorem landau_iff_unbounded : LandauNSqPlusOne ↔ ∀ N : ℕ, ∃ n, N < n ∧ (n ^ 2 + 1).Prime := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hlt, hp⟩ := h a
    exact ⟨n, hp, hlt⟩

theorem gcd_sq_add_one_succ_dvd_five (n : ℕ) : Nat.gcd (n ^ 2 + 1) ((n + 1) ^ 2 + 1) ∣ 5 := by
  set d := Nat.gcd (n ^ 2 + 1) ((n + 1) ^ 2 + 1) with hd
  have h1 : (d : ℤ) ∣ ((n : ℤ) ^ 2 + 1) := by
    have := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left (n ^ 2 + 1) ((n + 1) ^ 2 + 1))
    push_cast at this
    simpa [hd] using this
  have h2 : (d : ℤ) ∣ (((n : ℤ) + 1) ^ 2 + 1) := by
    have := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right (n ^ 2 + 1) ((n + 1) ^ 2 + 1))
    push_cast at this
    simpa [hd] using this
  have h5 : (d : ℤ) ∣ 5 := by
    have h := dvd_sub (h1.mul_left (2 * (n : ℤ) + 3)) (h2.mul_left (2 * (n : ℤ) - 1))
    have e : (2 * (n : ℤ) + 3) * ((n : ℤ) ^ 2 + 1)
        - (2 * (n : ℤ) - 1) * (((n : ℤ) + 1) ^ 2 + 1) = 5 := by ring
    rwa [e] at h
  exact_mod_cast h5

end Brockian.LandauProblem
