import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- `nu H p` is the number of distinct residue classes modulo `p` occupied by the
tuple `H`; in the Hardy–Littlewood singular series this is the quantity `ν_p(H)`
appearing in the local factor `(1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`. -/
def nu (H : Finset ℕ) (p : ℕ) : ℕ := (H.image (· % p)).card

/-- A finite tuple `H ⊆ ℕ` is *admissible* when for every prime `p` it misses at
least one residue class modulo `p`.  Equivalently, every local factor of the
singular series `𝔖(H)` is nonzero. -/
def Admissible (H : Finset ℕ) : Prop := ∀ p : ℕ, p.Prime → nu H p < p

/-- The local factor `(1 - ν_p(H)/p) (1 - 1/p)^{-|H|}` of the singular series. -/
noncomputable def localFactor (H : Finset ℕ) (p : ℕ) : ℝ :=
  (1 - (nu H p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ H.card

lemma nu_le_card (H : Finset ℕ) (p : ℕ) : nu H p ≤ H.card :=
  Finset.card_image_le

/-- A tuple of size smaller than `p` cannot cover all residues modulo `p`. -/
lemma nu_lt_of_card_lt {H : Finset ℕ} {p : ℕ} (h : H.card < p) : nu H p < p :=
  lt_of_le_of_lt (nu_le_card H p) h

/-- Admissibility only has to be checked at the primes `p ≤ |H|`. -/
lemma admissible_of_small_primes {H : Finset ℕ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → nu H p < p) : Admissible H := by
  intro p hp
  rcases Nat.lt_or_ge H.card p with hlt | hle
  · exact nu_lt_of_card_lt hlt
  · exact h p hp hle

/-- Every local factor of the singular series of an admissible tuple is positive. -/
lemma localFactor_pos {H : Finset ℕ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hnum : 0 < 1 - (nu H p : ℝ) / p := by
    have : (nu H p : ℝ) < p := by exact_mod_cast hH p hp
    have := (div_lt_one hp0).2 this
    linarith
  have hden : 0 < (1 - 1 / (p : ℝ)) ^ H.card := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]; exact hp1
    exact pow_pos (by linarith) _
  exact div_pos hnum hden

/-- The residue count modulo `p` of a pair `{0, d}`. -/
lemma nu_pair (d p : ℕ) : nu ({0, d} : Finset ℕ) p = ({0, d % p} : Finset ℕ).card := by
  simp [nu, Finset.image_insert, Nat.zero_mod]

/-- **Admissible gaps are exactly the even ones.**  The pair `{0, d}` is an
admissible `2`-tuple (equivalently, the singular series `𝔖(0, d)` is nonzero)
if and only if `d` is even. -/
lemma admissible_pair_iff (d : ℕ) : Admissible ({0, d} : Finset ℕ) ↔ Even d := by
  constructor
  · intro h
    by_contra hodd
    have h2 : d % 2 = 1 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hodd)
    have := h 2 Nat.prime_two
    rw [nu_pair, h2] at this
    simp at this
  · intro he p hp
    rcases eq_or_ne p 2 with rfl | hne
    · have h2 : d % 2 = 0 := Nat.even_iff.1 he
      rw [nu_pair, h2]
      simp
    · have h2p := hp.two_le
      have hp3 : 3 ≤ p := by omega
      refine nu_lt_of_card_lt (lt_of_le_of_lt ?_ (by omega : 2 < p))
      exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- The four-element tuple `{0, 1452, 1454, 1460}` is admissible. -/
lemma admissible_quadruple : Admissible ({0, 1452, 1454, 1460} : Finset ℕ) := by
  apply admissible_of_small_primes
  intro p hp hple
  have hcard : ({0, 1452, 1454, 1460} : Finset ℕ).card = 4 := by decide
  rw [hcard] at hple
  have h2 := hp.two_le
  interval_cases p
  · decide
  · decide
  · exact absurd hp (by decide)

/-!
## Main result
-/

/-- **Singular Series Gaps 1450–1460.**

Within the gap window `1450 ≤ d ≤ 1460`, the admissible gaps `d` — those for
which the pair `{0, d}` has a nonvanishing singular series — are exactly the six
even values `1450, 1452, 1454, 1456, 1458, 1460`; moreover the window supports a
genuinely larger admissible configuration, the `4`-tuple `{0, 1452, 1454, 1460}`,
all of whose singular-series local factors are strictly positive. -/
theorem SingularSeriesGaps14501460 :
    (∀ d : ℕ, 1450 ≤ d → d ≤ 1460 →
        (Admissible ({0, d} : Finset ℕ) ↔
          d ∈ ({1450, 1452, 1454, 1456, 1458, 1460} : Finset ℕ))) ∧
      Admissible ({0, 1452, 1454, 1460} : Finset ℕ) ∧
      (∀ p : ℕ, p.Prime → 0 < localFactor ({0, 1452, 1454, 1460} : Finset ℕ) p) := by
  refine ⟨?_, admissible_quadruple, fun p hp => localFactor_pos admissible_quadruple hp⟩
  intro d hd1 hd2
  rw [admissible_pair_iff, Nat.even_iff]
  constructor
  · intro h; interval_cases d <;> simp_all
  · intro h
    fin_cases h <;> rfl

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

