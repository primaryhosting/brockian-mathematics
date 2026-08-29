import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
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

/-- `nu H p` is the number of distinct residue classes modulo `p` occupied by the
finite set of integers `H`.  These are the local densities appearing in the singular
series `𝔖(H) = ∏_p (1 - nu H p / p) / (1 - 1/p)^{|H|}` of the Hardy–Littlewood
prime tuples conjecture. -/
noncomputable def nu (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image (fun h : ℤ => (h : ZMod p))).card

/-- A finite set of integers is *admissible* when, for every prime `p`, it fails to
occupy all residue classes modulo `p`.  Equivalently, no local factor of the
singular series `𝔖(H)` vanishes. -/
def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → nu H p < p

/-- If some residue class mod `p` is missed by `H`, then `nu H p < p`. -/
theorem nu_lt_of_missing_residue (H : Finset ℤ) (p : ℕ) [NeZero p] (r : ZMod p)
    (hr : ∀ h ∈ H, (h : ZMod p) ≠ r) : nu H p < p := by
  have hne : (H.image (fun h : ℤ => (h : ZMod p))) ≠ Finset.univ := by
    intro hcontra
    have hmem : r ∈ H.image (fun h : ℤ => (h : ZMod p)) := by
      rw [hcontra]; exact Finset.mem_univ r
    obtain ⟨h, hh, hhr⟩ := Finset.mem_image.1 hmem
    exact hr h hh hhr
  have := (Finset.card_lt_iff_ne_univ _).2 hne
  rwa [ZMod.card] at this

/-- If `nu H p < p` then some residue class mod `p` is missed by `H`. -/
theorem exists_missing_residue_of_nu_lt (H : Finset ℤ) (p : ℕ) [NeZero p]
    (h : nu H p < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  have hne : (H.image (fun h : ℤ => (h : ZMod p))) ≠ Finset.univ := by
    intro hcontra
    rw [nu, hcontra, Finset.card_univ, ZMod.card] at h
    exact lt_irrefl _ h
  have : ∃ r : ZMod p, r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
    by_contra hcon
    push_neg at hcon
    exact hne (Finset.eq_univ_iff_forall.2 hcon)
  obtain ⟨r, hr⟩ := this
  exact ⟨r, fun h hh hcontra => hr (Finset.mem_image.2 ⟨h, hh, hcontra⟩)⟩

/-- Admissibility, stated in the equivalent "missing residue" form: for each prime
`p` there is a residue class mod `p` avoided by `H`. -/
theorem isAdmissible_iff_exists_missing_residue (H : Finset ℤ) :
    IsAdmissible H ↔ ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    exact exists_missing_residue_of_nu_lt H p (hH p hp)
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hH p hp
    exact nu_lt_of_missing_residue H p r hr

/-- **Admissibility criterion.**  A set of primes, each of which exceeds the size of
the set, is admissible.  (For small primes `p` the residue class `0` is missed,
because every element is a prime larger than `p`; for large primes `p > |H|` there
are simply too few elements to cover all `p` classes.) -/
theorem isAdmissible_image_of_primes (S : Finset ℕ)
    (hprime : ∀ q ∈ S, Nat.Prime q) (hbig : ∀ q ∈ S, S.card < q) :
    IsAdmissible (S.image (fun q : ℕ => (q : ℤ))) := by
  have hcard : (S.image (fun q : ℕ => (q : ℤ))).card = S.card :=
    Finset.card_image_of_injective _ fun a b hab => by exact_mod_cast hab
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hle : p ≤ S.card
  · -- small prime: the residue class `0` is missed
    refine nu_lt_of_missing_residue _ p 0 ?_
    intro h hh
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hh
    have hq0 : ((q : ℤ) : ZMod p) = (q : ZMod p) := by push_cast; ring
    rw [hq0]
    intro hzero
    have hdvd : p ∣ q := (ZMod.natCast_eq_zero_iff q p).1 hzero
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hprime q hq)).1 hdvd
    have := hbig q hq
    omega
  · -- large prime: too few elements to cover all residues
    have h1 : nu (S.image (fun q : ℕ => (q : ℤ))) p ≤ S.card := by
      rw [nu, ← hcard]
      exact Finset.card_image_le
    omega

/-- **Singular Series Gaps 14501460.**

Inside the length-`10` window `[1450, 1460]` the three integers `1451, 1453, 1459`
form an admissible triple: every prime `p` misses at least one residue class of the
triple, so no local factor of the singular series `𝔖(H)` vanishes.  The triple has
diameter `8`, so `(0, 2, 8)` is an admissible gap pattern realised in this range. -/
theorem SingularSeriesGaps14501460 :
    ∃ H : Finset ℤ,
      IsAdmissible H ∧
      H.card = 3 ∧
      (∀ h ∈ H, (1450 : ℤ) ≤ h ∧ h ≤ 1460) ∧
      H = {1451, 1453, 1459} ∧
      (∃ a ∈ H, ∃ b ∈ H, b - a = 8) := by
  classical
  refine ⟨(({1451, 1453, 1459} : Finset ℕ).image (fun q : ℕ => (q : ℤ))), ?_, ?_, ?_, ?_, ?_⟩
  · refine isAdmissible_image_of_primes _ ?_ ?_
    · intro q hq
      fin_cases hq <;> norm_num
    · intro q hq
      have hc : ({1451, 1453, 1459} : Finset ℕ).card = 3 := by decide
      rw [hc]
      fin_cases hq <;> norm_num
  · decide
  · intro h hh
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hh
    obtain ⟨q, hq, rfl⟩ := hh
    rcases hq with rfl | rfl | rfl <;> norm_num
  · decide
  · exact ⟨1451, by decide, 1459, by decide, by norm_num⟩

end Brockian

