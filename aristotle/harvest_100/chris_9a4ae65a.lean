import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture: the associated singular series
is non-zero) when for every prime `p` the elements of `H` omit at least one
residue class modulo `p`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- A set with fewer elements than `p` can never cover all residues mod `p`. -/
theorem exists_missed_residue_of_card_lt {H : Finset ℕ} {p : ℕ} (hp : H.card < p) :
    ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hsub : Finset.range p ⊆ H.image (fun h => h % p) := by
    intro r hr
    rcases hcon r (Finset.mem_range.mp hr) with ⟨h, hh, hhr⟩
    exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
  have hcard : p ≤ H.card := by
    calc p = (Finset.range p).card := (Finset.card_range p).symm
      _ ≤ (H.image (fun h => h % p)).card := Finset.card_le_card hsub
      _ ≤ H.card := Finset.card_image_le
  omega

/-- Admissibility only needs to be checked at the primes `p ≤ |H|`. -/
theorem admissible_iff_small_primes (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  constructor
  · intro hH p hp _
    exact hH p hp
  · intro hH p hp
    rcases le_or_gt p H.card with hle | hgt
    · exact hH p hp hle
    · exact exists_missed_residue_of_card_lt hgt

/-- The explicit `k`-element candidate tuple `{0, k!, 2·k!, …, (k-1)·k!}`. -/
def factorialTuple (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => i * k !)

theorem card_factorialTuple (k : ℕ) : (factorialTuple k).card = k := by
  have hinj : Function.Injective (fun i : ℕ => i * k !) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) hab
  rw [factorialTuple, Finset.card_image_of_injective _ hinj, Finset.card_range]

theorem factorialTuple_le {k : ℕ} {h : ℕ} (hh : h ∈ factorialTuple k) :
    h ≤ (k - 1) * k ! := by
  rcases Finset.mem_image.mp hh with ⟨i, hi, rfl⟩
  have : i ≤ k - 1 := by
    have := Finset.mem_range.mp hi
    omega
  exact Nat.mul_le_mul_right _ this

theorem admissible_factorialTuple (k : ℕ) : Admissible (factorialTuple k) := by
  intro p hp
  rcases le_or_gt p k with hle | hgt
  · -- every element is divisible by `p`, so the class of `1` is missed
    refine ⟨1, hp.one_lt, ?_⟩
    intro h hh
    rcases Finset.mem_image.mp hh with ⟨i, _, rfl⟩
    have hdvd : p ∣ k ! := Nat.dvd_factorial hp.pos hle
    have : i * k ! % p = 0 := Nat.mod_eq_zero_of_dvd (hdvd.mul_left i)
    omega
  · exact exists_missed_residue_of_card_lt (by rw [card_factorialTuple]; exact hgt)

/-- **Singular Series Gaps 16021610.**

Two statements about admissible tuples (equivalently, tuples with non-vanishing
Hardy–Littlewood singular series):

* admissibility of `H` is decided by the primes `p ≤ |H|` alone;
* for every `k` there is an admissible `k`-tuple of natural numbers all lying in
  the gap range `[0, (k-1)·k!]`. -/
theorem SingularSeriesGaps16021610 :
    (∀ H : Finset ℕ,
        Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r < p, ∀ h ∈ H, h % p ≠ r) ∧
    (∀ k : ℕ, ∃ H : Finset ℕ, H.card = k ∧ (∀ h ∈ H, h ≤ (k - 1) * k !) ∧ Admissible H) := by
  refine ⟨admissible_iff_small_primes, fun k => ?_⟩
  exact ⟨factorialTuple k, card_factorialTuple k, fun _ hh => factorialTuple_le hh,
    admissible_factorialTuple k⟩

end Brockian

