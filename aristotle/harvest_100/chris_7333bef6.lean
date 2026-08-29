/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no imports at all), so that the
required header comment can literally be the first thing in the file.  Everything below is
built from the Lean 4 core library only.
-/

namespace Brockian

/-! ## Primality, admissible gap patterns -/

/-- Primality, spelled out from first principles: `p` is at least `2` and its only divisors
are `1` and `p`. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- A finite gap pattern `H` (a list of non-negative shifts) is **admissible** if, for every
prime `p`, some residue class `r mod p` contains no member of `H`.  Admissibility is exactly
the condition for the Hardy–Littlewood singular series attached to `H` to be non-zero: a
non-admissible pattern has a prime `p` whose residues are completely covered, which forces the
local factor at `p`, and hence the whole singular series, to vanish. -/
def Admissible (H : List Nat) : Prop :=
  ∀ p : Nat, IsPrime p → ∃ r : Nat, ∀ h ∈ H, h % p ≠ r % p

/-- The contrapositive reformulation of admissibility: `H` is admissible iff no prime has all of
its residue classes covered by `H`. -/
theorem admissible_iff_no_prime_covers (H : List Nat) :
    Admissible H ↔ ∀ p : Nat, IsPrime p → ¬ (∀ r : Nat, r < p → ∃ h ∈ H, h % p = r) := by
  constructor
  · intro hA p hp hcov
    obtain ⟨r, hr⟩ := hA p hp
    have hp0 : 0 < p := by have := hp.1; omega
    obtain ⟨h, hmem, hh⟩ := hcov (r % p) (Nat.mod_lt _ hp0)
    exact hr h hmem hh
  · intro hA p hp
    have hp0 : 0 < p := by have := hp.1; omega
    apply Classical.byContradiction
    intro hcon
    apply hA p hp
    intro r hr
    apply Classical.byContradiction
    intro hcon2
    exact hcon ⟨r, fun h hmem hh => hcon2 ⟨h, hmem, by rw [hh, Nat.mod_eq_of_lt hr]⟩⟩

/-! ## Elementary arithmetic facts -/

/-- Equal residues give a divisible difference. -/
theorem dvd_sub_of_mod_eq {p a b : Nat} (hm : a % p = b % p) : p ∣ (b - a) := by
  refine ⟨b / p - a / p, ?_⟩
  have h1 := Nat.div_add_mod b p
  have h2 := Nat.div_add_mod a p
  rw [Nat.mul_sub]
  omega

/-- A prime not dividing `m` is coprime to `m`. -/
theorem coprime_of_prime_not_dvd {p m : Nat} (hp : IsPrime p) (h : ¬ p ∣ m) :
    Nat.Coprime p m := by
  have hl := Nat.gcd_dvd_left p m
  have hr := Nat.gcd_dvd_right p m
  rcases hp.2 _ hl with h3 | h3
  · exact h3
  · exact absurd (h3 ▸ hr) h

/-! ## A family of admissible gap patterns -/

/-- The arithmetic-progression gap pattern `{0, M, 2M, …, (k-1)M}`, viewed as a set of shifts
inside the range `[0, (k-1)M]`. -/
def gapPattern (k M : Nat) : List Nat := (List.range k).map (fun i => i * M)

theorem mem_gapPattern {k M h : Nat} (hh : h ∈ gapPattern k M) : ∃ i, i < k ∧ h = i * M := by
  rw [gapPattern, List.mem_map] at hh
  obtain ⟨i, hi, rfl⟩ := hh
  exact ⟨i, List.mem_range.mp hi, rfl⟩

/-- **Singular Series Gaps 9098.**

New admissible gap ranges: for every common difference `M` that is divisible by all primes up
to the length `k`, the `k`-term arithmetic progression `{0, M, 2M, …, (k-1)M}` is an admissible
gap pattern, i.e. its Hardy–Littlewood singular series does not vanish.

The proof works via the contrapositive at each prime `p`: if `p ∣ M` the whole pattern sits in
the class `0 mod p`, so the class `1 mod p` is free; otherwise `p` is coprime to `M`, and the
class `k·M mod p` is free, since a collision would force `p ∣ k - i ≤ k`, hence `p ∣ M`. -/
theorem SingularSeriesGaps9098 (k M : Nat) (hM : ∀ p, IsPrime p → p ≤ k → p ∣ M) :
    Admissible (gapPattern k M) := by
  intro p hp
  have hp2 : 2 ≤ p := hp.1
  by_cases hpM : p ∣ M
  · refine ⟨1, ?_⟩
    intro h hh
    obtain ⟨i, -, rfl⟩ := mem_gapPattern hh
    have h0 : (i * M) % p = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hpM (Nat.dvd_mul_left M i))
    rw [h0, Nat.mod_eq_of_lt (by omega)]
    omega
  · refine ⟨k * M, ?_⟩
    intro h hh heq
    obtain ⟨i, hik, rfl⟩ := mem_gapPattern hh
    have hdvd : p ∣ (k * M - i * M) := dvd_sub_of_mod_eq heq
    have hfac : k * M - i * M = (k - i) * M := by
      rw [Nat.sub_mul]
    rw [hfac] at hdvd
    have hcop : Nat.Coprime p M := coprime_of_prime_not_dvd hp hpM
    have hki : p ∣ (k - i) := hcop.dvd_of_dvd_mul_right hdvd
    have hpos : 0 < k - i := by omega
    have hle : p ≤ k - i := Nat.le_of_dvd hpos hki
    exact hpM (hM p hp (by omega))

/-! ## Factorial differences and the concrete range of length 9098 -/

/-- Factorial, defined locally. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by decide
  | n + 1 => by
      have := fact_pos n
      simp only [fact]
      exact Nat.mul_pos (by omega) this

/-- Every positive number up to `k` divides `k!`. -/
theorem dvd_fact : ∀ (k m : Nat), 0 < m → m ≤ k → m ∣ fact k
  | 0, m, hm, hmk => by omega
  | k + 1, m, hm, hmk => by
      rcases Nat.eq_or_lt_of_le hmk with h | h
      · subst h
        exact ⟨fact k, rfl⟩
      · have hmk' : m ≤ k := by omega
        exact Nat.dvd_trans (dvd_fact k m hm hmk') (Nat.dvd_mul_left (fact k) (k + 1))

/-- With common difference `k!`, every length is allowed: the arithmetic progression
`{0, k!, 2·k!, …, (k-1)·k!}` is an admissible gap pattern. -/
theorem admissible_gapPattern_fact (k : Nat) : Admissible (gapPattern k (fact k)) := by
  apply SingularSeriesGaps9098
  intro p hp hpk
  exact dvd_fact k p (by have := hp.1; omega) hpk

/-- A concrete new admissible gap range: the `9098`-term progression with common difference
`9098!` is admissible. -/
theorem SingularSeriesGaps9098_instance :
    Admissible (gapPattern 9098 (fact 9098)) :=
  admissible_gapPattern_fact 9098

end Brockian

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

