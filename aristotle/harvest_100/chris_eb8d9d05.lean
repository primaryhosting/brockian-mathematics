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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Brockian
namespace GilbreathConjecture

/-! ## The Gilbreath triangle and the statement of the conjecture -/

/-- `gilbreathRow n k` is the `k`-th entry (0-indexed) of the `n`-th row of the
Gilbreath triangle: row `0` is the sequence of primes `2, 3, 5, 7, 11, ...` and each
subsequent row is obtained by taking absolute values of consecutive differences. -/
noncomputable def gilbreathRow : ℕ → ℕ → ℕ
  | 0, k => Nat.nth Nat.Prime k
  | (n + 1), k => Nat.dist (gilbreathRow n (k + 1)) (gilbreathRow n k)

@[simp] theorem gilbreathRow_zero (k : ℕ) :
    gilbreathRow 0 k = Nat.nth Nat.Prime k := rfl

@[simp] theorem gilbreathRow_succ (n k : ℕ) :
    gilbreathRow (n + 1) k = Nat.dist (gilbreathRow n (k + 1)) (gilbreathRow n k) := rfl

/-- **Gilbreath's conjecture**: every row of the Gilbreath triangle after the zeroth
one begins with `1`. -/
def GilbreathConjecture : Prop := ∀ n : ℕ, 1 ≤ n → gilbreathRow n 0 = 1

/-! ## Propagation of rows of the shape `1, {0,2}, {0,2}, …` -/

/-- `GoodRow n m` says that row `n` begins with `1` and that its next `m` entries all
lie in `{0, 2}`. This is the shape of row that is observed empirically (and verified
computationally, for very long prefixes, by Odlyzko). -/
def GoodRow (n m : ℕ) : Prop :=
  gilbreathRow n 0 = 1 ∧ ∀ i < m, gilbreathRow n (i + 1) = 0 ∨ gilbreathRow n (i + 1) = 2

theorem GoodRow.mono {n m m' : ℕ} (h : GoodRow n m) (hm : m' ≤ m) : GoodRow n m' :=
  ⟨h.1, fun i hi => h.2 i (lt_of_lt_of_le hi hm)⟩

/-- The distance between two elements of `{0, 2}` is again in `{0, 2}`. -/
theorem dist_mem_zero_two {a b : ℕ} (ha : a = 0 ∨ a = 2) (hb : b = 0 ∨ b = 2) :
    Nat.dist a b = 0 ∨ Nat.dist a b = 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [Nat.dist]

/-- The key propagation step: a good row of width `m + 1` produces a good row of
width `m` beneath it. -/
theorem GoodRow.step {n m : ℕ} (h : GoodRow n (m + 1)) : GoodRow (n + 1) m := by
  obtain ⟨h0, h2⟩ := h
  constructor
  · have h1 := h2 0 (Nat.succ_pos m)
    simp only [gilbreathRow_succ, h0]
    rcases h1 with h1 | h1 <;> simp [h1, Nat.dist]
  · intro i hi
    simp only [gilbreathRow_succ]
    exact dist_mem_zero_two (h2 (i + 1) (by omega)) (h2 i (by omega))

/-- Iterating the propagation step: if row `n` is good of width `m`, then row `n + m`
begins with `1`. -/
theorem GoodRow.head_add {n m : ℕ} (h : GoodRow n m) : gilbreathRow (n + m) 0 = 1 := by
  induction m generalizing n with
  | zero => simpa using h.1
  | succ m ih =>
      have hn : n + (m + 1) = (n + 1) + m := by omega
      rw [hn]
      exact ih h.step

/-- Any row lying between `n` and `n + m` begins with `1`, once row `n` is good of
width `m`. -/
theorem head_eq_one_of_goodRow {n m r : ℕ} (h : GoodRow n m) (h1 : n ≤ r) (h2 : r ≤ n + m) :
    gilbreathRow r 0 = 1 := by
  have h3 := (h.mono (show r - n ≤ m by omega)).head_add
  rwa [Nat.add_sub_cancel' h1] at h3

/-! ## A conditional reduction -/

/-- **Odlyzko's criterion**: for every `K ≥ 1` there is a row `n` with `1 ≤ n ≤ K`
which begins with `1` and whose following `K` entries all lie in `{0, 2}`. -/
def OdlyzkoCriterion : Prop := ∀ K : ℕ, 1 ≤ K → ∃ n, 1 ≤ n ∧ n ≤ K ∧ GoodRow n K

/-- **Conditional reduction of Gilbreath's conjecture.** If rows with arbitrarily long
`1, {0,2}, {0,2}, …` prefixes occur early enough (Odlyzko's criterion), then Gilbreath's
conjecture holds. -/
theorem gilbreath_of_odlyzko (h : OdlyzkoCriterion) : GilbreathConjecture := by
  intro r hr
  obtain ⟨n, _, hnr, hgood⟩ := h r hr
  have hg : GoodRow n (r - n) := hgood.mono (Nat.sub_le r n)
  have hh := hg.head_add
  rwa [Nat.add_sub_cancel' hnr] at hh

/-! ## An unconditional partial result: the first 108 rows

We verify Gilbreath's conjecture for rows `1, …, 108` by evaluating the triangle on the
first `109` primes. The propagation lemma `GoodRow.head_add` does most of the work: only
rows `1, 3, 5, 10, 11` need to be inspected, since each of them begins with `1` followed
by a long block of entries in `{0, 2}`.
-/

/-- The list of consecutive absolute differences of a list. -/
def diffs : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | a :: b :: t => Nat.dist b a :: diffs (b :: t)

theorem diffs_length : ∀ l : List ℕ, (diffs l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: b :: t => by simp [diffs, diffs_length (b :: t)]

theorem diffs_getD : ∀ (l : List ℕ) (k : ℕ), k + 1 < l.length →
    (diffs l).getD k 0 = Nat.dist (l.getD (k + 1) 0) (l.getD k 0)
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | _ :: _ :: _, 0, _ => by simp [diffs]
  | _ :: b :: t, (k + 1), h => by
      simp only [diffs, List.getD_cons_succ]
      exact diffs_getD (b :: t) k (by simpa using h)

/-- The first `109` primes. -/
def primeList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
   89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
   181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
   277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
   383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479,
   487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599]

theorem primeList_length : primeList.length = 109 := rfl

theorem nth_prime_eq_primeList (k : ℕ) (hk : k < 109) :
    Nat.nth Nat.Prime k = primeList.getD k 0 := by
  have hp : ∀ i < 109, Nat.Prime (primeList.getD i 0) := by decide
  have hc : ∀ i < 109, Nat.count Nat.Prime (primeList.getD i 0) = i := by decide
  have h := Nat.nth_count (hp k hk)
  rwa [hc k hk] at h

/-- A computable model of the rows of the Gilbreath triangle, truncated to the data
provided by the first `109` primes. -/
def rowList : ℕ → List ℕ
  | 0 => primeList
  | (n + 1) => diffs (rowList n)

theorem rowList_length (n : ℕ) : (rowList n).length = 109 - n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rowList, diffs_length, ih]; omega

/-- The computable model agrees with the Gilbreath triangle wherever it is defined. -/
theorem gilbreathRow_eq_rowList (n k : ℕ) (h : k + n < 109) :
    gilbreathRow n k = (rowList n).getD k 0 := by
  induction n generalizing k with
  | zero => exact nth_prime_eq_primeList k (by omega)
  | succ n ih =>
      have hlen : k + 1 < (rowList n).length := by rw [rowList_length]; omega
      rw [gilbreathRow_succ, ih (k + 1) (by omega), ih k (by omega), rowList,
        diffs_getD (rowList n) k hlen]

/-- A `GoodRow` fact can be read off from the computable model. -/
theorem goodRow_of_rowList {n m : ℕ} (hnm : n + m ≤ 108)
    (h0 : (rowList n).getD 0 0 = 1)
    (h2 : ∀ i < m, (rowList n).getD (i + 1) 0 = 0 ∨ (rowList n).getD (i + 1) 0 = 2) :
    GoodRow n m := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [gilbreathRow_eq_rowList n 0 (by omega)]; exact h0
  · rw [gilbreathRow_eq_rowList n (i + 1) (by omega)]; exact h2 i hi

theorem goodRow_one : GoodRow 1 2 :=
  goodRow_of_rowList (by norm_num) (by decide) (by decide)

theorem goodRow_three : GoodRow 3 13 :=
  goodRow_of_rowList (by norm_num) (by decide) (by decide)

theorem goodRow_five : GoodRow 5 24 :=
  goodRow_of_rowList (by norm_num) (by decide) (by decide)

theorem goodRow_ten : GoodRow 10 58 :=
  goodRow_of_rowList (by norm_num) (by decide) (by decide)

theorem goodRow_eleven : GoodRow 11 97 :=
  goodRow_of_rowList (by norm_num) (by decide) (by decide)

/-- **Unconditional partial result**: Gilbreath's conjecture holds for the first `108`
rows of the triangle. -/
theorem gilbreath_of_le_108 (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 108) : gilbreathRow n 0 = 1 := by
  by_cases h : n ≤ 3
  · exact head_eq_one_of_goodRow goodRow_one h1 (by omega)
  by_cases ha : n ≤ 16
  · exact head_eq_one_of_goodRow goodRow_three (by omega) (by omega)
  by_cases hb : n ≤ 29
  · exact head_eq_one_of_goodRow goodRow_five (by omega) (by omega)
  by_cases hc : n ≤ 68
  · exact head_eq_one_of_goodRow goodRow_ten (by omega) (by omega)
  · exact head_eq_one_of_goodRow goodRow_eleven (by omega) (by omega)

end GilbreathConjecture
end Brockian

