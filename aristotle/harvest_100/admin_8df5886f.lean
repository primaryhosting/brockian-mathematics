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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PolignacPrimes

/-- A finite list of linear forms `a * x + b` (encoded as pairs `(a, b)`) is *admissible*
if for every prime `p` there is some `x` for which no form takes a value divisible by `p`. -/
def Admissible (L : List (ℕ × ℕ)) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ x : ℕ, ∀ ab ∈ L, ¬ p ∣ (ab.1 * x + ab.2)

/-- **Dickson's conjecture** (the prime `k`-tuples hypothesis in its qualitative form):
for every admissible finite family of linear forms with positive leading coefficients,
there are infinitely many `x` at which all the forms are simultaneously prime. -/
def DicksonHypothesis : Prop :=
  ∀ L : List (ℕ × ℕ), (∀ ab ∈ L, 0 < ab.1) → Admissible L →
    {x : ℕ | ∀ ab ∈ L, Nat.Prime (ab.1 * x + ab.2)}.Infinite

/-- The set of primes `p` such that `p` and `p + n` are *consecutive* primes. -/
def PolignacSet (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ (p + n).Prime ∧ ∀ q, p < q → q < p + n → ¬ q.Prime}

/-- Sanity check that `PolignacSet` says what it should: `3` and `5` are consecutive primes,
so `3 ∈ PolignacSet 2`. -/
lemma three_mem_polignacSet_two : 3 ∈ PolignacSet 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q h1 h2
  interval_cases q
  · norm_num

/-- The `(n + 1 + j)`-th prime; used as a supply of distinct primes larger than `n`. -/
noncomputable def bigPrime (n j : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1 + j)

lemma bigPrime_prime (n j : ℕ) : (bigPrime n j).Prime := Nat.prime_nth_prime _

lemma bigPrime_gt (n j : ℕ) : n < bigPrime n j := by
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  have := hmono.le_apply (x := n + 1 + j)
  simp only [bigPrime]
  omega

lemma bigPrime_strictMono (n : ℕ) : StrictMono (bigPrime n) := by
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  intro i j hij
  exact hmono (by omega)

/-- The primes `bigPrime n j`, for varying `j`, are pairwise coprime. -/
lemma bigPrime_pairwise_coprime (n : ℕ) :
    List.Pairwise (Function.onFun Nat.Coprime (bigPrime n)) (List.range' 1 (n - 1)) := by
  refine List.Pairwise.imp ?_ (List.pairwise_lt_range' (s := 1) (n := n - 1))
  intro i j hij
  exact (Nat.coprime_primes (bigPrime_prime n i) (bigPrime_prime n j)).2
    (ne_of_lt (bigPrime_strictMono n hij))

/-- The key construction: for an even `n > 0` there are `M > 0` and `r` such that the pair of
forms `M x + r`, `M x + r + n` is admissible, and moreover every number strictly between
`M x + r` and `M x + r + n` is composite (for `x ≥ 2`). -/
lemma exists_admissible_pair (n : ℕ) (hn : Even n) (hpos : 0 < n) :
    ∃ M r : ℕ, 0 < M ∧ Admissible [(M, r), (M, r + n)] ∧
      ∀ x : ℕ, 2 ≤ x → ∀ q : ℕ, M * x + r < q → q < M * x + r + n → ¬ q.Prime := by
  classical
  set l : List ℕ := List.range' 1 (n - 1) with hl
  set q : ℕ → ℕ := bigPrime n with hqdef
  obtain ⟨r, hr⟩ :=
    Nat.chineseRemainderOfList (fun j => q j - j) q l (bigPrime_pairwise_coprime n)
  set M : ℕ := (l.map q).prod with hM
  have hmem : ∀ j, j ∈ l ↔ (1 ≤ j ∧ j < n) := by
    intro j
    rw [hl, List.mem_range'_1]
    omega
  have hqbig : ∀ j, n < q j := bigPrime_gt n
  have hqprime : ∀ j, (q j).Prime := bigPrime_prime n
  have hMpos : 0 < M := by
    rw [hM]
    apply List.prod_pos
    intro a ha
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    exact (hqprime j).pos
  have hdvdM : ∀ j ∈ l, q j ∣ M := fun j hj => List.dvd_prod (List.mem_map_of_mem hj)
  have hqle : ∀ j ∈ l, q j ≤ M := fun j hj => Nat.le_of_dvd hMpos (hdvdM j hj)
  have hdvdr : ∀ j ∈ l, q j ∣ r + j := by
    intro j hj
    have h := hr j hj
    have hj' : j ≤ q j := le_of_lt (lt_trans ((hmem j).1 hj).2 (hqbig j))
    have h2 : r + j ≡ q j - j + j [MOD q j] := h.add_right j
    rw [Nat.sub_add_cancel hj'] at h2
    have h4 : r + j ≡ 0 [MOD q j] := h2.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)
    exact Nat.modEq_zero_iff_dvd.1 h4
  refine ⟨M, r, hMpos, ?_, ?_⟩
  · -- admissibility
    intro p hp
    by_cases hpM : p ∣ M
    · obtain ⟨a, ha, hpa⟩ := (Nat.Prime.prime hp).dvd_prod_iff.1 hpM
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
      have hpj : p = q j := (Nat.prime_dvd_prime_iff_eq hp (hqprime j)).1 hpa
      obtain ⟨hj1, hj2⟩ := (hmem j).1 hj
      have hd : p ∣ r + j := hpj ▸ hdvdr j hj
      have hpn : n < p := hpj ▸ hqbig j
      refine ⟨0, ?_⟩
      intro ab hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
      rcases hab with rfl | rfl
      · simp only [Nat.mul_zero, Nat.zero_add]
        intro hpr
        have hj0 : p ∣ j := by simpa using Nat.dvd_sub hd hpr
        have := Nat.le_of_dvd (by omega) hj0
        omega
      · simp only [Nat.mul_zero, Nat.zero_add]
        intro hpr
        have hsub : (r + n) - (r + j) = n - j := by omega
        have hnj : p ∣ n - j := by
          have := Nat.dvd_sub hpr hd
          rwa [hsub] at this
        have := Nat.le_of_dvd (by omega) hnj
        omega
    · haveI : Fact p.Prime := ⟨hp⟩
      have hMne : (M : ZMod p) ≠ 0 := fun h => hpM ((ZMod.natCast_eq_zero_iff M p).1 h)
      obtain ⟨u, hu0, hun⟩ : ∃ u : ZMod p, u ≠ 0 ∧ u + (n : ZMod p) ≠ 0 := by
        by_cases h1 : (1 : ZMod p) + (n : ZMod p) = 0
        · have hncast : p = 2 → (n : ZMod p) = 0 := by
            rintro rfl
            exact (ZMod.natCast_eq_zero_iff n 2).2 hn.two_dvd
          have hp2 : p ≠ 2 := by
            intro h
            rw [hncast h, add_zero] at h1
            exact one_ne_zero h1
          refine ⟨2, ?_, ?_⟩
          · intro h
            have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
              ((ZMod.natCast_eq_zero_iff 2 p).1 h2))
          · have hrw : (2 : ZMod p) + (n : ZMod p) = ((1 : ZMod p) + (n : ZMod p)) + 1 := by ring
            rw [hrw, h1, zero_add]
            exact one_ne_zero
        · exact ⟨1, one_ne_zero, h1⟩
      set z : ZMod p := (u - (r : ZMod p)) * (M : ZMod p)⁻¹ with hz
      have hval : ((z.val : ℕ) : ZMod p) = z := by
        rw [ZMod.natCast_val, ZMod.cast_id]
      have hcast : (M : ZMod p) * ((z.val : ℕ) : ZMod p) + (r : ZMod p) = u := by
        rw [hval, hz]
        field_simp
        ring
      refine ⟨z.val, ?_⟩
      intro ab hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
      rcases hab with rfl | rfl
      · intro hdd
        have h0 := (ZMod.natCast_eq_zero_iff (M * z.val + r) p).2 hdd
        rw [Nat.cast_add, Nat.cast_mul, hcast] at h0
        exact hu0 h0
      · intro hdd
        have h0 := (ZMod.natCast_eq_zero_iff (M * z.val + (r + n)) p).2 hdd
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, ← add_assoc, hcast] at h0
        exact hun h0
  · -- the interval strictly between the two forms consists of composites
    intro x hx2 Q hQ1 hQ2
    set j := Q - (M * x + r) with hjdef
    have hjmem : j ∈ l := (hmem j).2 (by omega)
    have hQeq : Q = M * x + (r + j) := by omega
    have hd : q j ∣ Q := by
      rw [hQeq]
      exact Nat.dvd_add (Dvd.dvd.mul_right (hdvdM j hjmem) x) (hdvdr j hjmem)
    have hMx : M * 2 ≤ M * x := Nat.mul_le_mul_left M hx2
    have hqM : q j ≤ M := hqle j hjmem
    have hq2 : 2 ≤ q j := (hqprime j).two_le
    intro hQp
    rcases hQp.eq_one_or_self_of_dvd _ hd with h | h
    · exact absurd h (by omega)
    · omega

/-- **Polignac's conjecture**, conditional on Dickson's conjecture: for every even `n > 0`
there are infinitely many primes `p` such that `p` and `p + n` are consecutive primes. -/
theorem PolignacConjecture (hD : DicksonHypothesis) (n : ℕ) (hn : Even n) (hpos : 0 < n) :
    (PolignacSet n).Infinite := by
  obtain ⟨M, r, hM, hadm, hgap⟩ := exists_admissible_pair n hn hpos
  have hpos' : ∀ ab ∈ [(M, r), (M, r + n)], 0 < ab.1 := by
    intro ab hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
    rcases hab with h | h <;> simp [h, hM]
  have hS := hD _ hpos' hadm
  set S : Set ℕ := {x : ℕ | ∀ ab ∈ [(M, r), (M, r + n)], Nat.Prime (ab.1 * x + ab.2)} with hSdef
  have hS2 : (S \ {x : ℕ | x < 2}).Infinite := by
    apply hS.diff
    exact Set.finite_Iio 2
  have hmaps : (fun x => M * x + r) '' (S \ {x : ℕ | x < 2}) ⊆ PolignacSet n := by
    rintro p ⟨x, ⟨hxS, hx2⟩, rfl⟩
    have hx2' : 2 ≤ x := by simpa using hx2
    have h1 : Nat.Prime (M * x + r) := by
      have := hxS (M, r) (by simp)
      simpa using this
    have h2 : Nat.Prime (M * x + r + n) := by
      have := hxS (M, r + n) (by simp)
      simpa [add_assoc] using this
    exact ⟨h1, h2, hgap x hx2'⟩
  have hinj : Set.InjOn (fun x => M * x + r) (S \ {x : ℕ | x < 2}) := by
    intro a _ b _ hab
    simp only at hab
    have : M * a = M * b := by omega
    exact Nat.eq_of_mul_eq_mul_left hM this
  exact ((hS2.image hinj).mono hmaps)

end Brockian.PolignacPrimes

