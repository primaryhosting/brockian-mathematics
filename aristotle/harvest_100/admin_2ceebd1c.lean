/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-- The radical `rad n` of a natural number `n`: the product of the distinct primes
dividing `n`.  By convention `rad 0 = rad 1 = 1`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The set of `abc`-triples exceptional for the exponent `1 + ε`: triples `(a, b, c)` of
naturals with `a`, `b` positive and coprime, `a + b = c`, and `c > rad (a * b * c) ^ (1 + ε)`. -/
def abcExceptions (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
      ((rad (t.1 * t.2.1 * t.2.2) : ℝ)) ^ (1 + ε) < (t.2.2 : ℝ)}

/-- **The abc conjecture.**  For every `ε > 0` there are only finitely many triples of
positive coprime naturals `a`, `b` with `a + b = c` and `c > rad (a * b * c) ^ (1 + ε)`. -/
def ABCConjecture : Prop := ∀ ε : ℝ, 0 < ε → (abcExceptions ε).Finite

/-- The "effective" form of the abc conjecture: for every `ε > 0` there is a constant `K`
such that `c ≤ K * rad (a * b * c) ^ (1 + ε)` for all positive coprime `a`, `b` with
`a + b = c`. -/
def ABCEffective : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-! ### Basic facts about `rad` -/

/-- `rad` agrees with the radical of a unique factorization monoid. -/
theorem rad_eq_radical (n : ℕ) : rad n = UniqueFactorizationMonoid.radical n := by
  rw [rad, UniqueFactorizationMonoid.radical,
    UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]
  rfl

theorem one_le_rad (n : ℕ) : 1 ≤ rad n :=
  Finset.one_le_prod' fun _ hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le

theorem rad_dvd_self (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

theorem rad_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) : rad (m * n) = rad m * rad n := by
  simp only [rad_eq_radical]
  exact UniqueFactorizationMonoid.radical_mul (Nat.coprime_iff_isRelPrime.mp h)

theorem rad_two_pow {k : ℕ} (hk : k ≠ 0) : rad (2 ^ k) = 2 := by
  rw [rad_eq_radical, UniqueFactorizationMonoid.radical_pow_of_prime Nat.prime_two.prime hk]
  simp

/-- If `n` is positive and not squarefree, then twice its radical is at most `n`. -/
theorem two_mul_rad_le {n : ℕ} (hn : 0 < n) (h : ¬ Squarefree n) : 2 * rad n ≤ n := by
  obtain ⟨d, hd⟩ := rad_dvd_self n
  have hr : 0 < rad n := Nat.pos_of_ne_zero (by
    rw [rad_eq_radical]; exact UniqueFactorizationMonoid.radical_ne_zero)
  have hd2 : 2 ≤ d := by
    by_contra hlt
    push_neg at hlt
    interval_cases d
    · omega
    · exact h (by
        rw [show n = rad n by omega, rad_eq_radical]
        exact UniqueFactorizationMonoid.squarefree_radical)
  calc 2 * rad n = rad n * 2 := by ring
    _ ≤ rad n * d := Nat.mul_le_mul_left _ hd2
    _ = n := hd.symm

/-! ### The finiteness form and the effective form of the conjecture are equivalent -/

theorem abcConjecture_imp_abcEffective (h : ABCConjecture) : ABCEffective := by
  intro ε hε
  have hfin := (h ε hε).image (fun t => t.2.2)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨(N : ℝ) + 1, ?_⟩
  intro a b c ha hb hab habc
  have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := by exact_mod_cast one_le_rad _
  have hrp : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) :=
    Real.one_le_rpow hr1 (by linarith)
  by_cases hex : ((rad (a * b * c) : ℝ)) ^ (1 + ε) < (c : ℝ)
  · have hmem : ((a, b, c) : ℕ × ℕ × ℕ) ∈ abcExceptions ε := ⟨ha, hb, hab, habc, hex⟩
    have hcN : (c : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN ⟨_, hmem, rfl⟩
    calc (c:ℝ) ≤ (N:ℝ) + 1 := by linarith
      _ = ((N:ℝ) + 1) * 1 := by ring
      _ ≤ ((N:ℝ) + 1) * (rad (a * b * c) : ℝ) ^ (1 + ε) := by nlinarith
  · push_neg at hex
    calc (c:ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := hex
      _ ≤ ((N:ℝ) + 1) * (rad (a * b * c) : ℝ) ^ (1 + ε) := by nlinarith

theorem abcEffective_imp_abcConjecture (h : ABCEffective) : ABCConjecture := by
  intro ε hε
  obtain ⟨K, hK⟩ := h (ε / 2) (by linarith)
  set K' : ℝ := max K 1 with hK'def
  have hK1 : (1:ℝ) ≤ K' := le_max_right _ _
  have hK0 : (0:ℝ) < K' := by linarith
  have hK'' : ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ K' * (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by
    intro a b c ha hb hab habc
    have h1 := hK a b c ha hb hab habc
    have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := by exact_mod_cast one_le_rad _
    have hrp : (0:ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε / 2) :=
      Real.rpow_nonneg (by linarith) _
    have hKK : K ≤ K' := le_max_left _ _
    nlinarith
  set M : ℝ := K' ^ (2 / ε) with hMdef
  have hM0 : (0:ℝ) < M := Real.rpow_pos_of_pos hK0 _
  set B : ℝ := K' * M ^ (1 + ε / 2) with hBdef
  set N : ℕ := ⌈B⌉₊ + 1 with hNdef
  apply Set.Finite.subset (Finset.finite_toSet
    ((Finset.range N) ×ˢ (Finset.range N) ×ˢ (Finset.range N)))
  rintro ⟨a, b, c⟩ ⟨ha, hb, hab, habc, hexc⟩
  dsimp only at ha hb hab habc hexc
  have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := by exact_mod_cast one_le_rad _
  have hr0 : (0 : ℝ) < (rad (a * b * c) : ℝ) := by linarith
  set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
  have h2 := hK'' a b c ha hb hab habc
  have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0]; ring_nf
  have hpos : (0:ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
  have hlt : r ^ (ε / 2) < K' := by
    have hstep : r ^ (1 + ε / 2) * r ^ (ε / 2) < K' * r ^ (1 + ε / 2) := by
      rw [← hsplit]; linarith
    nlinarith
  have hrM : r ≤ M := by
    have hstep : (r ^ (ε / 2)) ^ (2 / ε) ≤ K' ^ (2 / ε) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hlt.le (by positivity)
    have hid : (r ^ (ε / 2)) ^ (2 / ε) = r := by
      rw [← Real.rpow_mul (by linarith)]
      have hee : (ε / 2) * (2 / ε) = 1 := by field_simp
      rw [hee, Real.rpow_one]
    rwa [hid] at hstep
  have hcB : (c : ℝ) ≤ B := by
    have hmono : r ^ (1 + ε / 2) ≤ M ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (by linarith) hrM (by linarith)
    calc (c:ℝ) ≤ K' * r ^ (1 + ε / 2) := h2
      _ ≤ K' * M ^ (1 + ε / 2) := by nlinarith
  have hcN : c < N := by
    have h1 : (c : ℝ) ≤ (⌈B⌉₊ : ℝ) := le_trans hcB (Nat.le_ceil B)
    have h2 : c ≤ ⌈B⌉₊ := by exact_mod_cast h1
    omega
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
  exact ⟨by omega, by omega, hcN⟩

/-! ### The exponent `1` (that is, `ε = 0`) admits infinitely many exceptions

The triples `1 + (64 ^ m - 1) = 64 ^ m` are exceptional for `ε = 0`: since `9 ∣ 64 ^ m - 1`,
the number `64 ^ m - 1` is not squarefree, so `2 * rad (64 ^ m - 1) ≤ 64 ^ m - 1`, while
`rad (1 * (64 ^ m - 1) * 64 ^ m) = 2 * rad (64 ^ m - 1)`. -/

theorem abcExceptions_zero_infinite : (abcExceptions 0).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((1 : ℕ), 64 ^ (n + 1) - 1, 64 ^ (n + 1))) ?_ ?_
  · intro m n hmn
    simp only [Prod.mk.injEq] at hmn
    have h64 : Function.Injective (fun k : ℕ => (64:ℕ) ^ k) :=
      fun x y hxy => Nat.pow_right_injective (by norm_num) hxy
    have := h64 hmn.2.2
    omega
  · intro n
    set m := n + 1 with hm
    have hc : (64:ℕ) ^ m = 2 ^ (6 * m) := by
      rw [pow_mul]; norm_num
    have hcpos : 64 ≤ (64:ℕ) ^ m := by
      calc (64:ℕ) = 64 ^ 1 := by norm_num
        _ ≤ 64 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    set b := (64:ℕ) ^ m - 1 with hb
    have hbpos : 0 < b := by omega
    have hsum : 1 + b = 64 ^ m := by omega
    have hcop : Nat.Coprime b (64 ^ m) := by
      have hbb : (64:ℕ) ^ m = b + 1 := by omega
      rw [hbb]
      simp
    have h9 : (9:ℕ) ∣ b := by
      have h1 := Nat.sub_dvd_pow_sub_pow 64 1 m
      simp at h1
      exact dvd_trans (by norm_num) h1
    have hnsq : ¬ Squarefree b := by
      intro hsq
      have h3 := hsq 3 (by simpa using h9)
      simp at h3
    have hrad : rad (1 * b * (64 ^ m)) = 2 * rad b := by
      rw [one_mul, rad_mul_of_coprime hcop, hc, rad_two_pow (by omega)]
      ring
    refine ⟨by norm_num, hbpos, by simp, by simpa using hsum, ?_⟩
    have hle : rad (1 * b * (64 ^ m)) < (64:ℕ) ^ m := by
      rw [hrad]
      have := two_mul_rad_le hbpos hnsq
      omega
    simp only [add_zero, Real.rpow_one]
    exact_mod_cast hle

/-- **The abc statement.**  The abc conjecture, stated as the finiteness, for every `ε > 0`,
of the set of exceptional triples `a + b = c` (with `a`, `b` positive and coprime) satisfying
`c > rad (a * b * c) ^ (1 + ε)`, is equivalent to its effective form `c ≤ K_ε * rad (abc) ^ (1+ε)`;
moreover the hypothesis `ε > 0` cannot be dropped: for `ε = 0` there are infinitely many
exceptional triples. -/
theorem abc_statement :
    (ABCConjecture ↔ ABCEffective) ∧ (abcExceptions 0).Infinite :=
  ⟨⟨abcConjecture_imp_abcEffective, abcEffective_imp_abcConjecture⟩,
    abcExceptions_zero_infinite⟩

end Frontier

