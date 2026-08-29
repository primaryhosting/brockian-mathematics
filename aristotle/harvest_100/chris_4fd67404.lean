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

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` to precede any module docstring, so the required header
-- comment appears both at the very top of the file (as a plain comment) and, verbatim,
-- as the module docstring just above.

namespace Brockian.PolignacPrimes

open Nat

/-- `PolignacPair p n` says that `p` and `p + n` are *consecutive* primes:
both are prime and no number strictly between them is prime. -/
def PolignacPair (p n : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + n) ∧ ∀ r, p < r → r < p + n → ¬ Nat.Prime r

/-- **Dickson's conjecture** for the pair of linear forms `A * x + B` and `A * x + B + n`:
if the pair is admissible (for every prime `q` some value of `x` makes neither form
divisible by `q`), then both forms are simultaneously prime for arbitrarily large `x`. -/
def DicksonPairHypothesis : Prop :=
  ∀ A B n : ℕ, 0 < A → 0 < n →
    (∀ q : ℕ, q.Prime → ∃ x : ℕ, ¬ q ∣ (A * x + B) ∧ ¬ q ∣ (A * x + B + n)) →
    ∀ N : ℕ, ∃ x : ℕ, N < x ∧ (A * x + B).Prime ∧ (A * x + B + n).Prime

section Construction

variable (n : ℕ)

/-- The auxiliary primes used to force the numbers strictly between `p` and `p + n`
to be composite: `auxPrime n j` is the `(n + j)`-th prime, in particular it exceeds `n`. -/
noncomputable def auxPrime (j : ℕ) : ℕ := Nat.nth Nat.Prime (n + j)

/-- The list of offsets `1, 2, …, n - 1`. -/
def offsets : List ℕ := List.range' 1 (n - 1)

/-- The modulus of the arithmetic progression: the product of the auxiliary primes. -/
noncomputable def modulus : ℕ := ((offsets n).map (auxPrime n)).prod

lemma auxPrime_prime (j : ℕ) : (auxPrime n j).Prime := Nat.prime_nth_prime _

lemma lt_auxPrime (j : ℕ) : n < auxPrime n j := by
  have := Nat.add_two_le_nth_prime (n + j)
  simp only [auxPrime]
  omega

lemma auxPrime_injective : Function.Injective (auxPrime n) := by
  intro i j h
  have := Nat.nth_injective Nat.infinite_setOf_prime h
  omega

lemma mem_offsets_iff (j : ℕ) : j ∈ offsets n ↔ 1 ≤ j ∧ j < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [offsets]
  · simp only [offsets, List.mem_range'_1]
    omega

lemma modulus_pos : 0 < modulus n := by
  refine List.prod_pos ?_
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨j, _, rfl⟩ := ha
  exact (auxPrime_prime n j).pos

lemma auxPrime_dvd_modulus {j : ℕ} (hj : j ∈ offsets n) : auxPrime n j ∣ modulus n :=
  List.dvd_prod (List.mem_map_of_mem hj)

lemma auxPrime_le_modulus {j : ℕ} (hj : j ∈ offsets n) : auxPrime n j ≤ modulus n :=
  Nat.le_of_dvd (modulus_pos n) (auxPrime_dvd_modulus n hj)

/-- The residue used for the offset `j`: it is `≡ -j` modulo `auxPrime n j`. -/
noncomputable def residue (j : ℕ) : ℕ := j * auxPrime n j - j

lemma offsets_pairwise_coprime :
    (offsets n).Pairwise (Function.onFun Nat.Coprime (auxPrime n)) := by
  have hnd : (offsets n).Nodup := by
    simpa [offsets] using List.nodup_range' (s := 1) (n := n - 1)
  refine List.Nodup.pairwise_of_forall_ne hnd ?_
  intro i _ j _ hij
  exact (Nat.coprime_primes (auxPrime_prime n i) (auxPrime_prime n j)).2
    (fun h => hij (auxPrime_injective n h))

/-- The starting point of the arithmetic progression: a solution of the
simultaneous congruences `B ≡ -j (mod auxPrime n j)` for `1 ≤ j ≤ n - 1`. -/
noncomputable def shift : ℕ :=
  (Nat.chineseRemainderOfList (residue n) (auxPrime n) (offsets n)
    (offsets_pairwise_coprime n) : ℕ)

lemma auxPrime_dvd_shift_add {j : ℕ} (hj : j ∈ offsets n) :
    auxPrime n j ∣ shift n + j := by
  have h : Nat.ModEq (auxPrime n j) (shift n) (residue n j) :=
    (Nat.chineseRemainderOfList (residue n) (auxPrime n) (offsets n)
      (offsets_pairwise_coprime n)).2 j hj
  have h2 : Nat.ModEq (auxPrime n j) (shift n + j) (residue n j + j) := h.add_right j
  have h3 : residue n j + j = j * auxPrime n j := by
    have : j ≤ j * auxPrime n j := Nat.le_mul_of_pos_right _ (auxPrime_prime n j).pos
    simp only [residue]
    omega
  have h4 : Nat.ModEq (auxPrime n j) (shift n + j) 0 := by
    rw [h3] at h2
    exact h2.trans ((Nat.modEq_zero_iff_dvd).2 ⟨j, by ring⟩)
  exact (Nat.modEq_zero_iff_dvd).1 h4

lemma not_auxPrime_dvd_shift {j : ℕ} (hj : j ∈ offsets n) : ¬ auxPrime n j ∣ shift n := by
  intro h
  have hd := auxPrime_dvd_shift_add n hj
  have hdj : auxPrime n j ∣ j := (Nat.dvd_add_right h).1 hd
  have hjlt : j < auxPrime n j :=
    lt_of_lt_of_le ((mem_offsets_iff n j).1 hj).2 (le_of_lt (lt_auxPrime n j))
  have hj1 : 1 ≤ j := ((mem_offsets_iff n j).1 hj).1
  have := Nat.le_of_dvd (by omega) hdj
  omega

lemma not_auxPrime_dvd_shift_add_n {j : ℕ} (hj : j ∈ offsets n) :
    ¬ auxPrime n j ∣ (shift n + n) := by
  intro h
  have hd := auxPrime_dvd_shift_add n hj
  obtain ⟨hj1, hjn⟩ := (mem_offsets_iff n j).1 hj
  have hsub : auxPrime n j ∣ (n - j) := by
    have hrw : shift n + n = (shift n + j) + (n - j) := by omega
    rw [hrw] at h
    exact (Nat.dvd_add_right hd).1 h
  have hlt : n - j < auxPrime n j := lt_of_le_of_lt (Nat.sub_le _ _) (lt_auxPrime n j)
  have := Nat.le_of_dvd (by omega) hsub
  omega

/-- Admissibility of the pair of linear forms built from `modulus n` and `shift n`. -/
lemma admissible (hn : Even n) (q : ℕ) (hq : q.Prime) :
    ∃ x : ℕ, ¬ q ∣ (modulus n * x + shift n) ∧ ¬ q ∣ (modulus n * x + shift n + n) := by
  by_cases hdvd : q ∣ modulus n
  · obtain ⟨a, ha, hqa⟩ := (Nat.Prime.prime hq).dvd_prod_iff.1 (by simpa [modulus] using hdvd)
    simp only [List.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hq_eq : q = auxPrime n j := (Nat.prime_dvd_prime_iff_eq hq (auxPrime_prime n j)).1 hqa
    subst hq_eq
    exact ⟨0, by simpa using not_auxPrime_dvd_shift n hj,
      by simpa using not_auxPrime_dvd_shift_add_n n hj⟩
  · haveI : Fact q.Prime := ⟨hq⟩
    have hA : (modulus n : ZMod q) ≠ 0 := fun h => hdvd ((ZMod.natCast_eq_zero_iff _ _).1 h)
    obtain ⟨t, ht0, htn⟩ : ∃ t : ZMod q, t ≠ 0 ∧ t + (n : ZMod q) ≠ 0 := by
      by_cases h1 : (1 : ZMod q) + (n : ZMod q) = 0
      · refine ⟨2, ?_, ?_⟩
        · have hq2 : q ≠ 2 := by
            rintro rfl
            rw [(ZMod.natCast_eq_zero_iff_even).2 hn, add_zero] at h1
            exact one_ne_zero h1
          have : ((2 : ℕ) : ZMod q) ≠ 0 := by
            rw [Ne, ZMod.natCast_eq_zero_iff]
            intro h
            exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
          simpa using this
        · have hrw : (2 : ZMod q) + (n : ZMod q) = 1 + (1 + (n : ZMod q)) := by ring
          rw [hrw, h1, add_zero]
          exact one_ne_zero
      · exact ⟨1, one_ne_zero, h1⟩
    refine ⟨ZMod.val ((t - (shift n : ZMod q)) * (modulus n : ZMod q)⁻¹), ?_, ?_⟩ <;>
      intro hcon <;>
      · have h0 := (ZMod.natCast_eq_zero_iff _ _).2 hcon
        push_cast [ZMod.natCast_val, ZMod.cast_id] at h0
        rw [mul_comm ((t - (shift n : ZMod q))) _, ← mul_assoc, mul_inv_cancel₀ hA, one_mul,
          sub_add_cancel] at h0
        first
          | exact ht0 h0
          | exact htn h0

end Construction

/-- **Polignac's conjecture**, conditional on Dickson's conjecture for pairs of
linear forms: for every positive even `n` there are infinitely many primes `p`
such that `p` and `p + n` are consecutive primes. -/
theorem PolignacConjecture (H : DicksonPairHypothesis) (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    {p : ℕ | PolignacPair p n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨x, hx, hp1, hp2⟩ := H (modulus n) (shift n) n (modulus_pos n) hn0
    (admissible n hn) (max N (modulus n))
  set p := modulus n * x + shift n with hpdef
  have hxp : x ≤ p := by
    have : x ≤ modulus n * x := Nat.le_mul_of_pos_left x (modulus_pos n)
    omega
  have hNp : N < p := by
    have : N < x := lt_of_le_of_lt (le_max_left _ _) hx
    omega
  have hMp : modulus n < p := by
    have : modulus n < x := lt_of_le_of_lt (le_max_right _ _) hx
    omega
  refine ⟨p, ⟨hp1, hp2, ?_⟩, hNp⟩
  intro r hr1 hr2 hrp
  obtain ⟨j, rfl⟩ : ∃ j, r = p + j := ⟨r - p, by omega⟩
  have hjmem : j ∈ offsets n := (mem_offsets_iff n j).2 (by omega)
  have hdvd : auxPrime n j ∣ p + j := by
    have hrw : p + j = modulus n * x + (shift n + j) := by rw [hpdef]; ring
    rw [hrw]
    exact Nat.dvd_add ((auxPrime_dvd_modulus n hjmem).mul_right x)
      (auxPrime_dvd_shift_add n hjmem)
  have hlt : auxPrime n j < p + j :=
    lt_of_le_of_lt (auxPrime_le_modulus n hjmem) (by omega)
  rcases (Nat.Prime.eq_one_or_self_of_dvd hrp _ hdvd) with h | h
  · exact (auxPrime_prime n j).one_lt.ne' h
  · omega

/-- A sanity check that `PolignacPair` is satisfiable: `3` and `5` are consecutive primes. -/
lemma polignacPair_three_two : PolignacPair 3 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro r h1 h2
  interval_cases r
  · norm_num

/-- Under Dickson's conjecture for pairs of linear forms, there are infinitely many
twin prime pairs. -/
theorem infinite_twin_primes (H : DicksonPairHypothesis) :
    {p : ℕ | PolignacPair p 2}.Infinite :=
  PolignacConjecture H 2 (by decide) (by norm_num)

end Brockian.PolignacPrimes

