/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

namespace Brockian

/-- A finite set `H` of integers is *admissible* when, for every prime `p`, the
reductions of the elements of `H` modulo `p` omit at least one residue class.
This is exactly the condition under which the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` is non-zero, i.e. the Hardy–Littlewood
prime `k`-tuples conjecture predicts infinitely many translates of `H` consisting
entirely of primes. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- Small primes never obstruct a set of primes all larger than its own size:
residue class `0` is missed. -/
theorem admissible_of_primes_small_case {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (hple : p ≤ H.card)
    (hH : ∀ h ∈ H, ∃ q : ℕ, q.Prime ∧ (q : ℤ) = h ∧ (H.card : ℤ) < h) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  refine ⟨0, ?_⟩
  intro h hh hzero
  obtain ⟨q, hq, hqh, hlt⟩ := hH h hh
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
  subst hqh
  have hdvd : p ∣ q := by exact_mod_cast hzero
  have hpq : p = q := ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  have : (H.card : ℤ) < (p : ℤ) := by rw [hpq]; exact hlt
  have : (H.card : ℤ) < (H.card : ℤ) := lt_of_lt_of_le this (by exact_mod_cast hple)
  exact absurd this (lt_irrefl _)

/-- Large primes never obstruct a set with fewer elements than the modulus:
by cardinality, some residue class is missed. -/
theorem admissible_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (hlt : H.card < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : (H.image (fun h : ℤ => (h : ZMod p))).card < Fintype.card (ZMod p) := by
    calc (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
      _ < p := hlt
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
  have hne : H.image (fun h : ℤ => (h : ZMod p)) ≠ Finset.univ := by
    intro hEq
    rw [hEq, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨r, -, hr⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (by simpa [Finset.card_univ] using hcard :
        (H.image (fun h : ℤ => (h : ZMod p))).card < (Finset.univ : Finset (ZMod p)).card)
  exact ⟨r, fun h hh hEq => hr (Finset.mem_image.mpr ⟨h, hh, hEq⟩)⟩

/-- **Singular Series Gaps 7280.**

Any finite set of (distinct) primes each of which exceeds the size of the set is an
admissible tuple; consequently one obtains admissible gap ranges of every shape
realised by such prime sets — in particular the five-element tuple
`{7, 11, 13, 17, 19}`, which lies inside the range `[0, 7280]`.

The two obstruction cases are closed by existing Mathlib lemmas:
`ZMod.intCast_zmod_eq_zero_iff_dvd` (small primes) and
`Finset.exists_mem_notMem_of_card_lt_card` together with `ZMod.card` (large primes). -/
theorem SingularSeriesGaps7280 :
    (∀ H : Finset ℤ,
        (∀ h ∈ H, ∃ q : ℕ, q.Prime ∧ (q : ℤ) = h ∧ (H.card : ℤ) < h) → Admissible H) ∧
      ∃ H : Finset ℤ, Admissible H ∧ H ⊆ Finset.Icc (0 : ℤ) 7280 ∧ H.card = 5 := by
  have general : ∀ H : Finset ℤ,
      (∀ h ∈ H, ∃ q : ℕ, q.Prime ∧ (q : ℤ) = h ∧ (H.card : ℤ) < h) → Admissible H := by
    intro H hH p hp
    rcases lt_or_ge H.card p with h | h
    · exact admissible_of_card_lt hp h
    · exact admissible_of_primes_small_case hp h hH
  refine ⟨general, ⟨({7, 11, 13, 17, 19} : Finset ℤ), ?_, ?_, ?_⟩⟩
  · have hcard : ({7, 11, 13, 17, 19} : Finset ℤ).card = 5 := by decide
    refine general _ ?_
    rw [hcard]
    intro h hh
    fin_cases hh
    · exact ⟨7, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨19, by norm_num, by norm_num, by norm_num⟩
  · intro h hh
    fin_cases hh <;> simp [Finset.mem_Icc]
  · decide

end Brockian

