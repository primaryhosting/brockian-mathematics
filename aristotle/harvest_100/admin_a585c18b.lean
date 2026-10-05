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

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.dupNamespace false

namespace Brockian
namespace GilbreathConjecture

/-!
## Setup

`gRow k n` is the `n`-th entry (0-indexed) of the `k`-th row of Gilbreath's triangle:
row `0` is the sequence of primes `2, 3, 5, 7, 11, …` and each subsequent row consists of the
absolute differences of consecutive entries of the previous row.

Gilbreath's conjecture states that every row of index `k ≥ 1` begins with `1`.
The conjecture is open; what is proved below is

* an unconditional verification for all rows of index `1 ≤ k ≤ 60`
  (`gilbreath_holds_below_61`), and
* the classical Odlyzko-style reduction (`GilbreathConjecture`): the conjecture follows from the
  hypothesis that for every `N ≥ 1` some row of index `k ≤ N` begins with `1` and has all of its
  next `N` entries equal to `0` or `2`.
-/

/-- The rows of Gilbreath's triangle: `gRow 0` enumerates the primes and
`gRow (k+1) n = |gRow k (n+1) - gRow k n|`. -/
noncomputable def gRow : ℕ → ℕ → ℕ
  | 0, n => Nat.nth Nat.Prime n
  | k + 1, n => Nat.dist (gRow k (n + 1)) (gRow k n)

/-- **Gilbreath's conjecture**: every row of index `k ≥ 1` of Gilbreath's triangle starts with `1`. -/
def GilbreathStatement : Prop := ∀ k, 1 ≤ k → gRow k 0 = 1

/-- Row `k` begins with `1` and its next `N` entries all lie in `{0, 2}`. -/
def CleanWindow (k N : ℕ) : Prop :=
  gRow k 0 = 1 ∧ ∀ i, 1 ≤ i → i ≤ N → gRow k i = 0 ∨ gRow k i = 2

/-- The hypothesis used by Odlyzko's verification method: for every `N ≥ 1` there is a row of
index `k` with `1 ≤ k ≤ N` which begins with `1` and whose next `N` entries are all `0` or `2`. -/
def OdlyzkoHypothesis : Prop := ∀ N, 1 ≤ N → ∃ k, 1 ≤ k ∧ k ≤ N ∧ CleanWindow k N

/-!
## The conditional reduction
-/

/-- A clean window propagates to the next row, with the window shortened by one. -/
lemma cleanWindow_succ {k N : ℕ} (h : CleanWindow k (N + 1)) : CleanWindow (k + 1) N := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, ?_⟩
  · have h2 := h1 1 le_rfl (by omega)
    show Nat.dist (gRow k 1) (gRow k 0) = 1
    rcases h2 with h | h <;> rw [h, h0] <;> decide
  · intro i hi hiN
    show Nat.dist (gRow k (i + 1)) (gRow k i) = 0 ∨ Nat.dist (gRow k (i + 1)) (gRow k i) = 2
    rcases h1 (i + 1) (by omega) (by omega) with h | h <;>
      rcases h1 i hi (by omega) with h' | h' <;> rw [h, h'] <;> decide

/-- A clean window of width `N` at row `k` forces the next `N` rows to begin with `1`. -/
lemma head_of_cleanWindow {k N : ℕ} (h : CleanWindow k N) : ∀ j, j ≤ N → gRow (k + j) 0 = 1 := by
  induction N generalizing k with
  | zero => intro j hj; interval_cases j; exact h.1
  | succ N ih =>
      intro j hj
      match j with
      | 0 => exact h.1
      | (j + 1) =>
        have e : k + (j + 1) = (k + 1) + j := by omega
        rw [e]
        exact ih (cleanWindow_succ h) j (by omega)

/-- **Conditional Gilbreath conjecture.** Under `OdlyzkoHypothesis` — for every `N ≥ 1` some row
of index `k ≤ N` begins with `1` followed by `N` entries all equal to `0` or `2` — every row of
Gilbreath's triangle of index `k ≥ 1` begins with `1`. -/
theorem GilbreathConjecture (H : OdlyzkoHypothesis) : GilbreathStatement := by
  intro m hm
  obtain ⟨k, hk1, hkm, hw⟩ := H m hm
  have h := head_of_cleanWindow hw (m - k) (by omega)
  rwa [show k + (m - k) = m from by omega] at h

/-!
## Unconditional verification of the first rows
-/

/-- The Gilbreath triangle built from an arbitrary starting sequence `f`. -/
def rowOf (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => f n
  | k + 1, n => Nat.dist (rowOf f k (n + 1)) (rowOf f k n)

lemma gRow_eq_rowOf : ∀ k n, gRow k n = rowOf (Nat.nth Nat.Prime) k n := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih => intro n; show Nat.dist _ _ = Nat.dist _ _; rw [ih, ih]

lemma rowOf_congr {f g : ℕ → ℕ} {m : ℕ} (h : ∀ n, n ≤ m → f n = g n) :
    ∀ k n, k + n ≤ m → rowOf f k n = rowOf g k n := by
  intro k
  induction k with
  | zero => intro n hn; exact h n (by omega)
  | succ k ih =>
      intro n hn
      show Nat.dist _ _ = Nat.dist _ _
      rw [ih (n + 1) (by omega), ih n (by omega)]

/-- Absolute differences of consecutive entries of a list. -/
def diffList : List ℕ → List ℕ
  | a :: b :: t => Nat.dist b a :: diffList (b :: t)
  | _ => []

/-- The segment `[rowOf f k n, …, rowOf f k (n + m - 1)]` of a row. -/
def seg (f : ℕ → ℕ) (k n m : ℕ) : List ℕ := (List.range m).map (fun i => rowOf f k (n + i))

lemma seg_succ (f : ℕ → ℕ) (k n m : ℕ) : seg f k n (m + 1) = rowOf f k n :: seg f k (n + 1) m := by
  have h : ((fun i => rowOf f k (n + i)) ∘ Nat.succ) = (fun i => rowOf f k (n + 1 + i)) := by
    funext i
    show rowOf f k (n + (i + 1)) = rowOf f k (n + 1 + i)
    congr 1
    omega
  rw [seg, seg, List.range_succ_eq_map, List.map_cons, List.map_map, h, Nat.add_zero]

lemma diffList_seg (f : ℕ → ℕ) (k : ℕ) :
    ∀ m n, diffList (seg f k n (m + 1)) = seg f (k + 1) n m := by
  intro m
  induction m with
  | zero => intro n; simp [seg, diffList]
  | succ m ih =>
      intro n
      rw [seg_succ, seg_succ, seg_succ]
      show Nat.dist _ _ :: diffList (rowOf f k (n + 1) :: seg f k (n + 1 + 1) m) = _
      rw [← seg_succ, ih (n + 1)]
      rfl

lemma iterate_diffList_seg (f : ℕ → ℕ) :
    ∀ k m n, diffList^[k] (seg f 0 n (m + k)) = seg f k n m := by
  intro k
  induction k with
  | zero => intro m n; simp
  | succ k ih =>
      intro m n
      rw [Function.iterate_succ_apply', show m + (k + 1) = (m + 1) + k from by omega, ih (m + 1) n,
        diffList_seg]

/-- The first 61 primes. -/
def primeList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
   197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283]

/-- A computable stand-in for the prime enumeration, valid for indices `≤ 60`. -/
def pf (n : ℕ) : ℕ := primeList.getD n 0

lemma nth_prime_of_count {p c : ℕ} (hp : Nat.Prime p) (hc : Nat.count Nat.Prime p = c) :
    Nat.nth Nat.Prime c = p := hc ▸ Nat.nth_count hp

lemma nth_prime_eq_pf : ∀ n, n ≤ 60 → Nat.nth Nat.Prime n = pf n := by
  intro n hn
  interval_cases n <;> exact nth_prime_of_count (by decide) (by decide)

lemma gRow_eq_rowOf_pf (k : ℕ) (hk : k ≤ 60) : gRow k 0 = rowOf pf k 0 := by
  rw [gRow_eq_rowOf]
  exact rowOf_congr (m := 60) nth_prime_eq_pf k 0 (by omega)

lemma rowOf_head (f : ℕ → ℕ) (k : ℕ) :
    rowOf f k 0 = (diffList^[k] (seg f 0 0 (1 + k))).headI := by
  rw [iterate_diffList_seg, seg_succ]
  simp [seg]

lemma head_check : ∀ k, k < 60 → (diffList^[k + 1] (seg pf 0 0 (1 + (k + 1)))).headI = 1 := by
  decide

/-- **Unconditional partial result**: rows `1` through `60` of Gilbreath's triangle begin with `1`. -/
theorem gilbreath_holds_below_61 : ∀ k, 1 ≤ k → k ≤ 60 → gRow k 0 = 1 := by
  intro k h1 h2
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [gRow_eq_rowOf_pf _ h2, rowOf_head]
  exact head_check j (by omega)

end GilbreathConjecture
end Brockian

