/-
  Brockian/AdmissibilityHLCriterion.lean — the Hardy–Littlewood admissibility criterion.

  Roadmap #11.  The core modules count, per modulus, the admissible start residues:
  `Brockian.Admissibility` (the single-gap `q − 2` law), `Brockian.AdmissibilityKTuple`
  (the general `q − |H|` law and its CRT lift), and the finite local wrapper in
  `Brockian.Admissibility.CriterionScaffold`.  Those are *local counts*.  This module
  proves the actual GLOBAL admissibility criterion for a finite integer tuple, in the
  standard Hardy–Littlewood form:

      a finite `H ⊆ ℤ` is admissible  ⟺  for every prime `p`, the image of `H` in
      `ZMod p` omits at least one residue class  ⟺  `ν_p(H) := |H mod p| < p`  for all `p`.

  The definition of admissibility taken here is the standard sieve one: `H` is admissible
  iff at no prime does its reduction cover *every* residue class (an uncovered class is a
  class the sieve can use).  Everything below is exact finite reasoning; no prime
  distribution, singular series, sieve asymptotic, or representation theorem is asserted.

  ## What is proved
  * `omitsResidue_iff_ne_univ` — omitting a residue class mod `p` = the image is not all
    of `ZMod p` (rules out any vacuous reading of "omits").
  * `omitsResidue_iff_nu_lt` — omitting a class mod `p` ⟺ `ν_p(H) < p` (for `p ≠ 0`),
    the finite-cardinality heart of the criterion.
  * `admissible_iff_nu_lt` / `admissible_iff_card_image_lt` — **the criterion**:
    `Admissible H ↔ ∀ p prime, ν_p(H) < p`, stated both via `ν` and verbatim as
    `∀ p prime, (H.image (· : ZMod p)).card < p`.
  * `admissible_iff_nu_lt_of_le_card` — **the finiteness reduction**: it suffices to
    check primes `p ≤ |H|` (for larger primes `ν_p(H) ≤ |H| < p` automatically), so
    admissibility is verifiable from finitely many local checks.
  * `admissible_iff_exists_avoiding_start` — connects to the per-modulus count: `H` is
    admissible ⟺ at every prime there is a start residue `a` with `a + h ≠ 0` for all
    occupied classes `h` (reusing the scaffold's `LocalTupleAdmissible`).
  * `admissible_iff_count_pos` — the count form: `H` is admissible ⟺ at every prime the
    `q − ν` admissible-residue count of `Brockian.AdmissibilityKTuple` is positive.
  * `admissible_zero_two` — `{0,2}` is admissible (COMPUTATION for the one local check).
  * `not_admissible_zero_two_four` — `{0,2,4}` is inadmissible: mod 3 it covers all
    residues (COMPUTATION for `ν_3 = 3`).

  ## What is NOT proved
  * No claim that admissible tuples are realized by primes infinitely often (that is the
    open Hardy–Littlewood conjecture, not the admissibility criterion). This module is the
    combinatorial criterion only.
  * No singular-series constant, density, or asymptotic count is derived.
  * The iterated multi-prime CRT product `∏ (pᵢ − νᵢ)` is in `AdmissibilityKTuple`
    (2-factor); it is not re-derived or extended here.

  Verification (spec §2A):
    - `#print axioms` : [propext, Classical.choice, Quot.sound]  (clean; the two example
      lemmas use kernel `decide` on small `ZMod` computations — COMPUTATION register)
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib
import Brockian.Admissibility
import Brockian.AdmissibilityKTuple
import Brockian.AdmissibilityCriterionScaffold

set_option autoImplicit false

open Finset
open Brockian.AdmissibilityKTuple
open Brockian.Admissibility.CriterionScaffold

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/
def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `ν_p(H)`: the number of distinct residue classes mod `p` occupied by `H`. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- `H` *omits a residue class* mod `p`: some residue mod `p` is not occupied by `H`. -/
def OmitsResidue (p : ℕ) (H : Finset ℤ) : Prop :=
  ∃ r : ZMod p, r ∉ residueImage p H

/-- **Admissibility (Hardy–Littlewood).** A finite integer tuple `H` is admissible iff
for every prime `p` it omits at least one residue class mod `p` (equivalently, at no
prime does its reduction cover every residue class). -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → OmitsResidue p H

/-- Omitting a residue class mod `p` means exactly that the occupied image is not all of
`ZMod p`.  This pins down the intended meaning of "omits". -/
theorem omitsResidue_iff_ne_univ (p : ℕ) [NeZero p] (H : Finset ℤ) :
    OmitsResidue p H ↔ residueImage p H ≠ Finset.univ := by
  unfold OmitsResidue
  constructor
  · rintro ⟨r, hr⟩ hcov
    exact hr (hcov ▸ Finset.mem_univ r)
  · intro hne
    by_contra hc
    push_neg at hc
    exact hne (Finset.eq_univ_iff_forall.mpr hc)

/-- Omitting a residue class mod a nonzero modulus `p` is equivalent to the finite
inequality `ν_p(H) < p`. -/
theorem omitsResidue_iff_nu_lt (p : ℕ) [NeZero p] (H : Finset ℤ) :
    OmitsResidue p H ↔ nu p H < p := by
  rw [omitsResidue_iff_ne_univ]
  have h : (residueImage p H).card < Fintype.card (ZMod p)
      ↔ residueImage p H ≠ Finset.univ :=
    Finset.card_lt_iff_ne_univ _
  rw [ZMod.card] at h
  exact h.symm

/-- **The Hardy–Littlewood admissibility criterion (ν form).** A finite integer tuple is
admissible iff at every prime it occupies fewer than `p` residue classes. -/
theorem admissible_iff_nu_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → nu p H < p := by
  unfold Admissible
  constructor
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    exact (omitsResidue_iff_nu_lt p H).mp (h p hp)
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    exact (omitsResidue_iff_nu_lt p H).mpr (h p hp)

/-- **The criterion, verbatim.** `H` is admissible iff for every prime `p` the image of
`H` in `ZMod p` has fewer than `p` elements. -/
theorem admissible_iff_card_image_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → (H.image (fun n : ℤ => (n : ZMod p))).card < p :=
  admissible_iff_nu_lt H

/-- **The finiteness reduction.** Admissibility only needs checking at primes `p ≤ |H|`:
for a prime `p > |H|` we have `ν_p(H) ≤ |H| < p` automatically.  Hence admissibility is
decided by finitely many local checks. -/
theorem admissible_iff_nu_lt_of_le_card (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → nu p H < p := by
  rw [admissible_iff_nu_lt]
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    by_cases hle : p ≤ H.card
    · exact h p hp hle
    · push_neg at hle
      calc nu p H ≤ H.card := Finset.card_image_le
        _ < p := hle

/-- **Connection to the per-modulus count (existence form).** `H` is admissible iff at
every prime there is a start residue avoiding every occupied class — i.e. some `a` with
`a + h ≠ 0` for all `h` in the reduction of `H`.  This is exactly the local admissible
start of `Brockian.Admissibility.CriterionScaffold`. -/
theorem admissible_iff_exists_avoiding_start (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime →
      ∃ a : ZMod p, ∀ h ∈ residueImage p H, a + h ≠ 0 := by
  rw [admissible_iff_nu_lt]
  constructor
  · intro hcrit p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    have hla : LocalTupleAdmissible p (residueImage p H) := by
      rw [localTupleAdmissible_iff_obstruction_lt]
      exact hcrit p hp
    exact (localTupleAdmissible_iff_exists_avoids _).mp hla
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    have hla : LocalTupleAdmissible p (residueImage p H) :=
      (localTupleAdmissible_iff_exists_avoids _).mpr (h p hp)
    rw [localTupleAdmissible_iff_obstruction_lt] at hla
    exact hla

/-- **Connection to the `q − ν` count.** `H` is admissible iff at every prime the number
of admissible start residues (`p − ν_p(H)`, the count of `Brockian.AdmissibilityKTuple`)
is strictly positive. -/
theorem admissible_iff_count_pos (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, ∀ hp : p.Prime,
      letI : NeZero p := ⟨hp.pos.ne'⟩
      0 < (admissibleTupleResidues p (residueImage p H)).card := by
  rw [admissible_iff_nu_lt]
  have hnu : ∀ p, nu p H = (residueImage p H).card := fun _ => rfl
  constructor
  · intro hcrit p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    rw [admissibleTupleResidues_card]
    have := hcrit p hp
    have := hnu p
    omega
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    have hc := h p hp
    rw [admissibleTupleResidues_card] at hc
    have := hnu p
    omega

/-- **COMPUTATION.** `{0, 2}` is admissible.  By the finiteness reduction only the prime
`p = 2` needs checking, and mod 2 the tuple occupies a single class (`ν_2 = 1 < 2`). -/
theorem admissible_zero_two : Admissible ({0, 2} : Finset ℤ) := by
  rw [admissible_iff_nu_lt_of_le_card]
  intro p hp hle
  have hcard : ({0, 2} : Finset ℤ).card = 2 := by decide
  rw [hcard] at hle
  have hp2 : p = 2 := le_antisymm hle hp.two_le
  subst hp2
  decide

/-- **COMPUTATION.** `{0, 2, 4}` is inadmissible: modulo 3 it occupies all three residue
classes (`ν_3 = 3`), so it omits none. -/
theorem not_admissible_zero_two_four : ¬ Admissible ({0, 2, 4} : Finset ℤ) := by
  intro h
  have h3 := (admissible_iff_nu_lt _).mp h 3 (by norm_num)
  have hnu3 : nu 3 ({0, 2, 4} : Finset ℤ) = 3 := by decide
  omega

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- The nine-element offset set `{0, 1, 3, 5, 9, 11, 15, 17, 21}` is not admissible:
it covers both residue classes mod `2`. -/
theorem firstNinePrimeOffsets_not_admissible :
    ¬ Admissible ({0, 1, 3, 5, 9, 11, 15, 17, 21} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 2 Nat.prime_two
  revert hr
  revert r
  decide






theorem admissible_image_add_const (S : Finset ℤ) (c : ℤ)
    (h : Admissible S) : Admissible (S.image (· + c)) := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  refine ⟨r + (c : ZMod p), ?_⟩
  intro hmem
  apply hr
  simp only [residueImage, Finset.mem_image, Finset.image_image] at hmem ⊢
  obtain ⟨s, hs, hs2⟩ := hmem
  refine ⟨s, hs, ?_⟩
  simp only [Function.comp_apply, Int.cast_add] at hs2
  exact add_right_cancel hs2






theorem not_admissible_of_five_consecutive_mod_five :
    ¬ Admissible ({0, 1, 2, 3, 4} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 5 (by norm_num)
  revert hr
  revert r
  decide






/-- Negation acts as a bijection on residues mod every prime, so it preserves
admissibility. -/
theorem admissible_image_neg (S : Finset ℤ) (h : Admissible S) :
    Admissible (S.image (fun x => -x)) := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  refine ⟨-r, fun hmem => hr ?_⟩
  simp only [residueImage, Finset.mem_image, Finset.image_image, Function.comp] at hmem ⊢
  obtain ⟨x, hx, hxe⟩ := hmem
  exact ⟨x, hx, by push_cast at hxe ⊢; linear_combination -hxe⟩






theorem residueImage_subset {S T : Finset ℤ} (p : ℕ) (hT : T ⊆ S) :
    residueImage p T ⊆ residueImage p S :=
  Finset.image_subset_image hT

theorem admissible_of_subset {S T : Finset ℤ} (h : Admissible S)
    (hT : T ⊆ S) : Admissible T := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  exact ⟨r, fun hmem => hr (residueImage_subset p hT hmem)⟩






theorem not_admissible_of_all_residues_mod_seven :
    ¬ Admissible ({0, 1, 9, 10, 11, 12, 20} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 7 (by norm_num)
  exact hr (by revert r; decide)

/-
  Target theorem `nu_image_add_const` for the corpus module
  `Brockian.AdmissibilityHLCriterion`.

  The corpus modules themselves (`Brockian.Admissibility`, `Brockian.AdmissibilityKTuple`,
  `Brockian.AdmissibilityCriterionScaffold`) are not part of this project, so the two
  corpus definitions the goal is phrased in terms of (`residueImage` and `nu`) are
  reproduced here verbatim, in their original namespace, purely so that the statement
  elaborates.  Nothing else from the corpus is restated or re-proved.
-/




namespace Brockian.AdmissibilityHLCriterion

/-- Translating a finite integer tuple by a constant `c` leaves the local count `ν_p`
unchanged: reduction mod `p` turns the translation into addition of `(c : ZMod p)`,
which is a bijection of `ZMod p`. -/
theorem nu_image_add_const (p : ℕ) (S : Finset ℤ) (c : ℤ) :
    nu p (S.image (fun x => x + c)) = nu p S := by
  unfold nu residueImage
  rw [Finset.image_image]
  have h : (S.image ((fun n : ℤ => (n : ZMod p)) ∘ (fun x => x + c)))
      = (S.image (fun n : ℤ => (n : ZMod p))).image (fun y => y + (c : ZMod p)) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    simp
  rw [h, Finset.card_image_of_injective _ (add_left_injective _)]







namespace Brockian.AdmissibilityHLCriterion

/-- **COMPUTATION.** The eleven-term arithmetic progression `12 · i` (`i = 0, …, 10`)
covers every residue class mod `11` (since `12 ≡ 1 [ZMOD 11]`), so it is inadmissible. -/
theorem not_admissible_of_eleven_dilated_residues :
    ¬ Admissible ({0, 12, 24, 36, 48, 60, 72, 84, 96, 108, 120} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 11 (by norm_num)
  exact hr (by revert r; decide)

end Brockian.AdmissibilityHLCriterion

end Brockian.AdmissibilityHLCriterion


/-- Membership in the mod-`p` residue image of an affine image of `S`. -/
theorem mem_residueImage_image_affine (a b : ℤ) (S : Finset ℤ) (p : ℕ) (z : ZMod p) :
    z ∈ residueImage p (S.image (fun x => a * x + b)) ↔
      ∃ x ∈ S, (a : ZMod p) * (x : ZMod p) + (b : ZMod p) = z := by
  simp only [residueImage, Finset.mem_image, Finset.image_image, Function.comp_apply,
    Int.cast_add, Int.cast_mul]


/-- **Affine invariance of admissibility.** For any integers `a`, `b`, the affine image
`a • S + b` of an admissible set `S` is admissible.  If `p ∤ a` the map is a bijection of
`ZMod p`, so the omitted class is transported; if `p ∣ a` the image collapses to the
single class of `b`, which cannot exhaust `ZMod p` since `p ≥ 2`. -/
theorem admissible_image_affine (a b : ℤ) {S : Finset ℤ}
    (h : Admissible S) : Admissible (S.image (fun x => a * x + b)) := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases ha : (a : ZMod p) = 0
  · refine ⟨(b : ZMod p) + 1, ?_⟩
    rw [mem_residueImage_image_affine]
    rintro ⟨x, -, hxe⟩
    rw [ha, zero_mul, zero_add] at hxe
    exact one_ne_zero (α := ZMod p) (by linear_combination -hxe)
  · obtain ⟨r, hr⟩ := h p hp
    refine ⟨(a : ZMod p) * r + (b : ZMod p), ?_⟩
    rw [mem_residueImage_image_affine]
    rintro ⟨x, hx, hxe⟩
    refine hr ?_
    have hrx : (x : ZMod p) = r := by
      have : (a : ZMod p) * ((x : ZMod p) - r) = 0 := by linear_combination hxe
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 ha
      · exact sub_eq_zero.mp h1
    rw [← hrx]
    exact Finset.mem_image_of_mem _ hx


/-- Reflecting a finite integer tuple through the origin leaves the local count `ν_p`
unchanged: reduction mod `p` turns `x ↦ -x` into negation on `ZMod p`, which is a
bijection of `ZMod p`. -/
theorem nu_image_neg (p : ℕ) (S : Finset ℤ) :
    nu p (S.image (fun x => -x)) = nu p S := by
  unfold nu residueImage
  rw [Finset.image_image]
  have h : (S.image ((fun n : ℤ => (n : ZMod p)) ∘ (fun x => -x)))
      = (S.image (fun n : ℤ => (n : ZMod p))).image (fun y => -y) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    simp
  rw [h, Finset.card_image_of_injective _ (neg_injective)]


/-- If the reduction map is injective on `S` and `S` has at least `p` elements, then
`S` meets every residue class mod `p`, i.e. `ν_p(S) = p`. -/
theorem nu_eq_of_injOn_card_ge (p : ℕ) [NeZero p] (S : Finset ℤ)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, ((x : ZMod p) = (y : ZMod p)) → x = y)
    (hcard : p ≤ S.card) :
    nu p S = p := by
  have hcardeq : nu p S = S.card :=
    Finset.card_image_of_injOn (fun x hx y hy hxy => hinj x hx y hy hxy)
  have hle : nu p S ≤ p := by
    have := Finset.card_le_univ (residueImage p S)
    simpa [nu, ZMod.card] using this
  omega


/-- **COMPUTATION.** The thirteen-element set `{0, 3, 8, 12, 14, 23, 30, 35, 37, 44, 45,
54, 59}` reduces mod `13` to the residues `0, 3, 8, 12, 1, 10, 4, 9, 11, 5, 6, 2, 7`,
i.e. to all of `ZMod 13`, so it omits no residue class mod `13` and is inadmissible. -/
theorem not_admissible_of_thirteen_scattered_residues :
    ¬ Admissible ({0, 3, 8, 12, 14, 23, 30, 35, 37, 44, 45, 54, 59} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 13 (by norm_num)
  exact hr (by revert r; decide)


/-- Subadditivity of the local count `ν_p` under unions. -/
theorem nu_union_le (p : ℕ) (S T : Finset ℤ) :
    nu p (S ∪ T) ≤ nu p S + nu p T := by
  unfold nu residueImage
  rw [Finset.image_union]
  exact Finset.card_union_le _ _


/-- Dilating a finite integer tuple by an integer `a` that is not divisible by the prime
`p` leaves the local count `ν_p` unchanged: reduction mod `p` turns the dilation into
multiplication by the nonzero element `(a : ZMod p)` of the field `ZMod p`, which is a
bijection of `ZMod p`. -/
theorem nu_image_mul_of_not_dvd {p : ℕ} (hp : p.Prime) (a : ℤ)
    (ha : ¬ ((p : ℤ) ∣ a)) (S : Finset ℤ) :
    nu p (S.image (fun x => a * x)) = nu p S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha0 : (a : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold nu residueImage
  rw [Finset.image_image]
  have h : (S.image ((fun n : ℤ => (n : ZMod p)) ∘ (fun x => a * x)))
      = (S.image (fun n : ℤ => (n : ZMod p))).image (fun y => (a : ZMod p) * y) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    simp
  rw [h, Finset.card_image_of_injective _ (mul_right_injective₀ ha0)]

end Brockian.AdmissibilityHLCriterion
