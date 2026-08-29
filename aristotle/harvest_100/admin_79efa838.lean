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

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

/-! ## Basic definitions

Everything below is developed from first principles (no imports), so that the
module docstring above can legally be the first thing in the file. -/

/-- The predicate selecting the positive divisors of `n`. -/
def isDivisor (n d : Nat) : Bool := decide (0 < d ∧ n % d = 0)

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n, d > 0} d`.  (`σ 0 = 0`.) -/
def sigmaSum (n : Nat) : Nat := ((List.range (n + 1)).filter (isDivisor n)).sum

/-- The *quasi-aliquot* map `s*(n) = σ(n) - n - 1`: the sum of the divisors of `n`
other than `1` and `n` itself. -/
def quasiAliquot (n : Nat) : Nat := sigmaSum n - n - 1

/-- `m` and `n` form a **betrothed** (quasi-amicable) pair: both exceed `1`, they are
distinct, and `σ(m) = σ(n) = m + n + 1`. -/
def Betrothed (m n : Nat) : Prop :=
  1 < m ∧ 1 < n ∧ m ≠ n ∧ sigmaSum m = m + n + 1 ∧ sigmaSum n = m + n + 1

/-- `n` is **quasi-perfect** if `σ(n) = 2n + 1`, i.e. `n` is a fixed point of the
quasi-aliquot map.  No quasi-perfect number is known; their nonexistence is a
classical conjecture. -/
def QuasiPerfect (n : Nat) : Prop := sigmaSum n = 2 * n + 1

/-- There are infinitely many betrothed pairs. -/
def BetrothedInfinite : Prop := ∀ N : Nat, ∃ m n : Nat, N < m ∧ Betrothed m n

/-- The quasi-aliquot map has infinitely many points on `2`-cycles. -/
def QuasiCycleInfinite : Prop :=
  ∀ N : Nat, ∃ n : Nat, N < n ∧ 1 < n ∧ quasiAliquot (quasiAliquot n) = n

/-! ## Elementary arithmetic of `σ` -/

theorem sum_append_nat : ∀ (l1 l2 : List Nat), (l1 ++ l2).sum = l1.sum + l2.sum := by
  intro l1
  induction l1 with
  | nil => intro l2; simp
  | cons a t ih => intro l2; simp only [List.cons_append, List.sum_cons, ih]; omega

theorem le_sum_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons a t ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp [List.sum_cons]
      · have := ih hx'
        simp only [List.sum_cons]
        omega

theorem sigmaSum_zero : sigmaSum 0 = 0 := rfl

theorem sigmaSum_one : sigmaSum 1 = 1 := rfl

theorem quasiAliquot_zero : quasiAliquot 0 = 0 := rfl

theorem quasiAliquot_one : quasiAliquot 1 = 0 := rfl

/-- Splitting off the divisor `n` itself. -/
theorem sigmaSum_eq_add_self {n : Nat} (hn : 0 < n) :
    sigmaSum n = ((List.range n).filter (isDivisor n)).sum + n := by
  unfold sigmaSum
  rw [List.range_succ, List.filter_append, sum_append_nat]
  have : (List.filter (isDivisor n) [n]) = [n] := by
    simp [List.filter, isDivisor, hn, Nat.mod_self]
  rw [this]
  simp

/-- For `n > 1` both `1` and `n` are divisors of `n`, hence `σ(n) ≥ n + 1`. -/
theorem succ_le_sigmaSum {n : Nat} (hn : 1 < n) : n + 1 ≤ sigmaSum n := by
  have hmem : (1 : Nat) ∈ (List.range n).filter (isDivisor n) := by
    rw [List.mem_filter]
    refine ⟨List.mem_range.mpr hn, ?_⟩
    simp [isDivisor, Nat.mod_one]
  have h1 := le_sum_of_mem hmem
  have h2 := sigmaSum_eq_add_self (n := n) (by omega)
  omega

/-- For `n > 1`, `σ(n) = s*(n) + n + 1`. -/
theorem sigmaSum_eq_quasiAliquot_add {n : Nat} (hn : 1 < n) :
    sigmaSum n = quasiAliquot n + n + 1 := by
  have := succ_le_sigmaSum hn
  simp only [quasiAliquot]
  omega

/-! ## Betrothed pairs as `2`-cycles of the quasi-aliquot map -/

/-- Betrothedness, restated as a `2`-cycle condition for the quasi-aliquot map. -/
theorem betrothed_iff {m n : Nat} (hm : 1 < m) (hn : 1 < n) :
    Betrothed m n ↔ m ≠ n ∧ quasiAliquot m = n ∧ quasiAliquot n = m := by
  have h1 := sigmaSum_eq_quasiAliquot_add hm
  have h2 := sigmaSum_eq_quasiAliquot_add hn
  constructor
  · rintro ⟨-, -, hne, hsm, hsn⟩
    exact ⟨hne, by omega, by omega⟩
  · rintro ⟨hne, hqm, hqn⟩
    exact ⟨hm, hn, hne, by omega, by omega⟩

/-- Betrothedness is symmetric. -/
theorem Betrothed.symm {m n : Nat} (h : Betrothed m n) : Betrothed n m := by
  obtain ⟨hm, hn, hne, hsm, hsn⟩ := h
  exact ⟨hn, hm, fun hc => hne hc.symm, by omega, by omega⟩

/-- In a betrothed pair the partner is determined by `s*`. -/
theorem Betrothed.snd_eq {m n : Nat} (h : Betrothed m n) : quasiAliquot m = n := by
  obtain ⟨hm, -, -, hsm, -⟩ := h
  have := sigmaSum_eq_quasiAliquot_add hm
  omega

/-- Each member of a betrothed pair lies on a `2`-cycle of `s*`. -/
theorem Betrothed.quasiCycle {m n : Nat} (h : Betrothed m n) :
    1 < m ∧ quasiAliquot (quasiAliquot m) = m := by
  refine ⟨h.1, ?_⟩
  rw [h.snd_eq, h.symm.snd_eq]

/-- No member of a betrothed pair has `σ(m) = m + 1` (in particular, primes and `1`
never occur in a betrothed pair). -/
theorem Betrothed.sigmaSum_ne {m n : Nat} (h : Betrothed m n) : sigmaSum m ≠ m + 1 := by
  obtain ⟨-, hn, -, hsm, -⟩ := h
  omega

/-- A point on a `2`-cycle of `s*` has image `> 1`. -/
theorem one_lt_quasiAliquot {n : Nat} (hn1 : 1 < n)
    (hcyc : quasiAliquot (quasiAliquot n) = n) : 1 < quasiAliquot n := by
  match hq : quasiAliquot n with
  | 0 => rw [hq, quasiAliquot_zero] at hcyc; omega
  | 1 => rw [hq, quasiAliquot_one] at hcyc; omega
  | (k + 2) => omega

/-- Assuming no quasi-perfect numbers exist, every `2`-cycle point of `s*` yields a
genuine betrothed pair. -/
theorem betrothed_of_quasiCycle (hQP : ∀ k : Nat, ¬ QuasiPerfect k) {n : Nat} (hn1 : 1 < n)
    (hcyc : quasiAliquot (quasiAliquot n) = n) : Betrothed n (quasiAliquot n) := by
  have hq1 : 1 < quasiAliquot n := one_lt_quasiAliquot hn1 hcyc
  refine (betrothed_iff hn1 hq1).mpr ⟨?_, rfl, hcyc⟩
  intro hEq
  refine hQP n ?_
  have h := sigmaSum_eq_quasiAliquot_add hn1
  unfold QuasiPerfect
  omega

/-! ## Examples -/

theorem sigmaSum_48 : sigmaSum 48 = 124 := by decide

theorem sigmaSum_75 : sigmaSum 75 = 124 := by decide

theorem sigmaSum_140 : sigmaSum 140 = 336 := by decide

theorem sigmaSum_195 : sigmaSum 195 = 336 := by decide

theorem betrothed_48_75 : Betrothed 48 75 :=
  ⟨by omega, by omega, by omega, sigmaSum_48, sigmaSum_75⟩

theorem betrothed_140_195 : Betrothed 140 195 :=
  ⟨by omega, by omega, by omega, sigmaSum_140, sigmaSum_195⟩

set_option maxRecDepth 20000 in
theorem sigmaSum_1050 : sigmaSum 1050 = 2976 := by decide

set_option maxRecDepth 20000 in
theorem sigmaSum_1925 : sigmaSum 1925 = 2976 := by decide

theorem betrothed_1050_1925 : Betrothed 1050 1925 :=
  ⟨by omega, by omega, by omega, sigmaSum_1050, sigmaSum_1925⟩

set_option maxRecDepth 20000 in
theorem sigmaSum_1575 : sigmaSum 1575 = 3224 := by decide

set_option maxRecDepth 20000 in
theorem sigmaSum_1648 : sigmaSum 1648 = 3224 := by decide

theorem betrothed_1575_1648 : Betrothed 1575 1648 :=
  ⟨by omega, by omega, by omega, sigmaSum_1575, sigmaSum_1648⟩

set_option maxRecDepth 20000 in
theorem sigmaSum_2024 : sigmaSum 2024 = 4320 := by decide

set_option maxRecDepth 20000 in
theorem sigmaSum_2295 : sigmaSum 2295 = 4320 := by decide

theorem betrothed_2024_2295 : Betrothed 2024 2295 :=
  ⟨by omega, by omega, by omega, sigmaSum_2024, sigmaSum_2295⟩

set_option maxRecDepth 40000 in
theorem sigmaSum_5775 : sigmaSum 5775 = 11904 := by decide

set_option maxRecDepth 40000 in
theorem sigmaSum_6128 : sigmaSum 6128 = 11904 := by decide

theorem betrothed_5775_6128 : Betrothed 5775 6128 :=
  ⟨by omega, by omega, by omega, sigmaSum_5775, sigmaSum_6128⟩

/-! ## The reduction -/

/-- **Betrothed Infinitude (conditional reduction).**
Assume no quasi-perfect number exists (`σ(k) ≠ 2k + 1` for all `k`; a classical
conjecture, verified far beyond every computed range).  Then there are infinitely
many betrothed (quasi-amicable) pairs if and only if the quasi-aliquot map
`s*(n) = σ(n) - n - 1` has infinitely many points lying on `2`-cycles. -/
theorem BetrothedInfinitude (hQP : ∀ k : Nat, ¬ QuasiPerfect k) :
    BetrothedInfinite ↔ QuasiCycleInfinite := by
  constructor
  · intro h N
    obtain ⟨m, n, hNm, hb⟩ := h N
    exact ⟨m, hNm, hb.quasiCycle.1, hb.quasiCycle.2⟩
  · intro h N
    obtain ⟨n, hNn, hn1, hcyc⟩ := h N
    exact ⟨n, quasiAliquot n, hNn, betrothed_of_quasiCycle hQP hn1 hcyc⟩

end Brockian.BetrothedNumbers

