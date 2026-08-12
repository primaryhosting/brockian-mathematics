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

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` **misses a residue class** modulo `p` if there is an
integer `r` such that no element of `H` is congruent to `r` modulo `p`. -/
def MissesResidue (H : Finset ℤ) (p : ℕ) : Prop :=
  ∃ r : ℤ, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (h - r))

/-- Hardy–Littlewood **admissibility** of a tuple of integers: for every prime `p`, the
elements of `H` do not cover all residue classes modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → MissesResidue H p

/-- If a finite set of integers has fewer elements than the prime `p`, then it cannot
cover all residue classes modulo `p`. -/
theorem missesResidue_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (hcard : H.card < p) : MissesResidue H p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set S : Finset (ZMod p) := H.image (fun x : ℤ => (x : ZMod p)) with hS
  have hSlt : S.card < Fintype.card (ZMod p) := by
    have h1 : S.card ≤ H.card := Finset.card_image_le
    have h2 : Fintype.card (ZMod p) = p := ZMod.card p
    omega
  have hex : ∃ r : ZMod p, r ∉ S := by
    by_contra hcon
    push_neg at hcon
    have : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hcon
    rw [this, Finset.card_univ] at hSlt
    exact lt_irrefl _ hSlt
  obtain ⟨r, hr⟩ := hex
  refine ⟨(r.val : ℤ), ?_⟩
  intro h hh hdvd
  apply hr
  have hcast : (((r.val : ℤ)) : ZMod p) = r := by push_cast; simp
  have : ((h : ZMod p)) = r := by
    have := (ZMod.intCast_eq_intCast_iff h (r.val : ℤ) p).mpr
      (Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp hdvd))
    rw [this, hcast]
  rw [hS, ← this]
  exact Finset.mem_image_of_mem _ hh

/-- **Admissibility criterion for 4-tuples.**  A set of four integers is admissible
(in the sense of the prime `k`-tuple conjecture) if and only if it misses a residue
class modulo `2` and modulo `3`; all larger primes impose no condition. -/
theorem AdmissibilityKTupleK4 {H : Finset ℤ} (hcard : H.card = 4) :
    Admissible H ↔ (MissesResidue H 2 ∧ MissesResidue H 3) := by
  constructor
  · intro hA
    exact ⟨hA 2 Nat.prime_two, hA 3 Nat.prime_three⟩
  · rintro ⟨h2, h3⟩ p hp
    rcases lt_trichotomy p 5 with hlt | heq | hgt
    · -- p ∈ {2, 3} since p is prime and p < 5
      interval_cases p
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
      · exact h2
      · exact h3
      · exact absurd hp (by decide)
    · exact missesResidue_of_card_lt hp (by omega)
    · exact missesResidue_of_card_lt hp (by omega)

/-- The classical prime-quadruplet pattern `{0, 2, 6, 8}` is an admissible 4-tuple. -/
theorem admissible_zero_two_six_eight :
    Admissible ({0, 2, 6, 8} : Finset ℤ) := by
  have hcard : ({0, 2, 6, 8} : Finset ℤ).card = 4 := by decide
  rw [AdmissibilityKTupleK4 hcard]
  constructor
  · refine ⟨1, ?_⟩
    intro h hh
    fin_cases hh <;> decide
  · refine ⟨1, ?_⟩
    intro h hh
    fin_cases hh <;> decide

end Brockian

