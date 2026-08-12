import Mathlib
import Archive.Sensitivity

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

/-!
# Huang's sensitivity theorem: degree is at most sensitivity squared

We formalize the sensitivity conjecture (Huang, 2019) for Boolean functions
`f : (ι → Bool) → Bool` on a finite set `ι` of variables:

  `degree f ≤ (sensitivity f)^2`.

Here `degree f` is the Fourier degree: the largest cardinality of a set `S` of variables
whose Fourier–Walsh coefficient `fourierCoeff f S` is non-zero (equivalently, the degree
of the unique multilinear real polynomial representing `f`), and `sensitivity f` is the
maximum over inputs `x` of the number of coordinates `i` such that flipping `x i`
changes the value of `f`.

The combinatorial core (Huang's degree theorem on the hypercube: every set of more than
half of the vertices of the `n`-dimensional hypercube induces a subgraph with a vertex of
degree at least `√n`) is taken from `Archive.Sensitivity`.  The remaining work here is the
Gotsman–Linial style reduction from the sensitivity conjecture to that theorem:

* transferring Huang's theorem from the cube `Fin n → Bool` to a cube `ι → Bool` indexed by
  an arbitrary finite type (`Frontier.huang_flip`);
* the top-degree case: if the top Fourier coefficient of `f` is non-zero, then
  `√(card ι) ≤ sensitivity f` (`Frontier.sqrt_card_le_sensitivity_of_top_coeff`);
* the restriction argument: a non-zero coefficient at `S` survives in some restriction of
  the variables outside `S`, and restricting does not increase sensitivity.
-/

namespace Frontier

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Basic definitions -/

/-- Flip the `i`-th coordinate of a point of the hypercube. -/
def flipAt (x : ι → Bool) (i : ι) : ι → Bool := Function.update x i (!x i)

/-- The sensitivity of `f` at the point `x`: the number of coordinates whose flip changes
the value of `f`. -/
def sensitivityAt (f : (ι → Bool) → Bool) (x : ι → Bool) : ℕ :=
  #{i ∈ (univ : Finset ι) | f (flipAt x i) ≠ f x}

/-- The sensitivity of a Boolean function: the maximum of its sensitivity over all inputs. -/
def sensitivity (f : (ι → Bool) → Bool) : ℕ :=
  (univ : Finset (ι → Bool)).sup (fun x => sensitivityAt f x)

/-- The `± 1` encoding of a Boolean value. -/
def bsign (b : Bool) : ℝ := if b then -1 else 1

/-- The Fourier–Walsh character indexed by a set `S` of coordinates. -/
def chi (S : Finset ι) (x : ι → Bool) : ℝ := ∏ i ∈ S, bsign (x i)

/-- The Fourier–Walsh coefficient of `f` at `S`. -/
noncomputable def fourierCoeff (f : (ι → Bool) → Bool) (S : Finset ι) : ℝ :=
  (2 ^ Fintype.card ι : ℝ)⁻¹ * ∑ x : ι → Bool, bsign (f x) * chi S x

/-- The (Fourier) degree of a Boolean function: the largest size of a set of coordinates
with a non-zero Fourier coefficient. -/
noncomputable def degree (f : (ι → Bool) → Bool) : ℕ :=
  {S ∈ (univ : Finset (Finset ι)) | fourierCoeff f S ≠ 0}.sup Finset.card

/-! ## Elementary lemmas -/

omit [Fintype ι] in
theorem flipAt_apply (x : ι → Bool) (i j : ι) :
    flipAt x i j = if j = i then !x i else x j := by
  simp [flipAt, Function.update_apply]

omit [Fintype ι] in
@[simp] theorem flipAt_self (x : ι → Bool) (i : ι) : flipAt x i i = !x i := by
  simp [flipAt]

omit [Fintype ι] in
theorem flipAt_of_ne {x : ι → Bool} {i j : ι} (h : j ≠ i) : flipAt x i j = x j := by
  simp [flipAt_apply, h]

omit [Fintype ι] in
theorem flipAt_ne_self (x : ι → Bool) (i : ι) : flipAt x i ≠ x := by
  intro h
  have := congrFun h i
  simp at this

omit [Fintype ι] in
theorem flipAt_injective (x : ι → Bool) : Function.Injective (flipAt x) := by
  intro i j h
  by_contra hij
  have h1 := congrFun h i
  rw [flipAt_self, flipAt_of_ne hij] at h1
  simp at h1

theorem bsign_not (b : Bool) : bsign (!b) = -bsign b := by
  cases b <;> simp [bsign]

theorem bsign_ne_zero (b : Bool) : bsign b ≠ 0 := by
  cases b <;> norm_num [bsign]

theorem bsign_eq_bsign_iff (a b : Bool) : bsign a = bsign b ↔ a = b := by
  cases a <;> cases b <;> norm_num [bsign]

theorem chi_flipAt (x : ι → Bool) (i : ι) :
    chi (univ : Finset ι) (flipAt x i) = -chi (univ : Finset ι) x := by
  have hi : i ∈ (univ : Finset ι) := mem_univ i
  have h1 : chi (univ : Finset ι) (flipAt x i)
      = bsign (!x i) * ∏ j ∈ univ.erase i, bsign (x j) := by
    rw [chi, ← Finset.mul_prod_erase _ _ hi, flipAt_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [flipAt_of_ne (Finset.ne_of_mem_erase hj)]
  have h2 : chi (univ : Finset ι) x = bsign (x i) * ∏ j ∈ univ.erase i, bsign (x j) :=
    (Finset.mul_prod_erase _ _ hi).symm
  rw [h1, h2, bsign_not]
  ring

/-! ## Huang's degree theorem on an arbitrary finite cube -/

omit [Fintype ι] in
theorem eq_flipAt_of_unique_ne {x p : ι → Bool} {i : ι} (hi : x i ≠ p i)
    (huniq : ∀ u, x u ≠ p u → u = i) : p = flipAt x i := by
  funext u
  by_cases hu : u = i
  · subst hu
    rw [flipAt_self]
    cases hxu : x u <;> cases hpu : p u <;> simp_all
  · rw [flipAt_of_ne hu]
    by_contra hne
    exact hu (huniq u fun h => hne h.symm)

/-- Huang's degree theorem in the standard cube, phrased with coordinate flips. -/
theorem huang_fin (m : ℕ) (A : Finset (Fin (m + 1) → Bool)) (hA : 2 ^ m < A.card) :
    ∃ x ∈ A, Real.sqrt (m + 1) ≤ #{i ∈ (univ : Finset (Fin (m + 1))) | flipAt x i ∈ A} := by
  let A₀ : Finset (Sensitivity.Q (m + 1)) := A
  obtain ⟨q, hqH, hq⟩ :=
    Sensitivity.huang_degree_theorem (m := m) (↑A₀ : Set (Sensitivity.Q (m + 1))) (by
      rw [Set.toFinset_card]
      simpa [A₀] using hA)
  have hqA : q ∈ A := by simpa [A₀] using hqH
  refine ⟨q, hqA, le_trans hq (Nat.cast_le.mpr ?_)⟩
  refine Finset.card_le_card_of_surjOn (fun i => flipAt q i) ?_
  intro p hp
  simp only [Finset.mem_coe, Set.mem_toFinset] at hp
  obtain ⟨hpA, i, hi, huniq⟩ := hp
  have hpflip : p = flipAt q i := eq_flipAt_of_unique_ne hi huniq
  refine ⟨i, ?_, hpflip.symm⟩
  simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
  rw [← hpflip]
  exact hpA

/-- Huang's degree theorem, in the cube indexed by an arbitrary finite type and phrased
with coordinate flips: if `A` contains more than half of the points of the cube, then some
point of `A` has at least `√(card ι)` neighbours in `A`. -/
theorem huang_flip (A : Finset (ι → Bool)) (hA : 2 ^ (Fintype.card ι - 1) < A.card) :
    ∃ x ∈ A, Real.sqrt (Fintype.card ι) ≤ #{i ∈ (univ : Finset ι) | flipAt x i ∈ A} := by
  have hcard_le : A.card ≤ 2 ^ Fintype.card ι := by
    have h := Finset.card_le_card (Finset.subset_univ A)
    simpa [Finset.card_univ] using h
  -- the hypothesis forces the cube to have positive dimension
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · rw [h0] at hA hcard_le
      norm_num at hA hcard_le
      omega
    · exact ⟨Fintype.card ι - 1, by omega⟩
  -- transport everything to the standard cube `Fin (m+1) → Bool`
  let e : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
  let E : (ι → Bool) ≃ (Fin (m + 1) → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  have hE : ∀ (x : ι → Bool) (j : Fin (m + 1)), E x j = x (e.symm j) := fun _ _ => rfl
  have hEflip : ∀ (x : ι → Bool) (i : ι), E (flipAt x i) = flipAt (E x) (e i) := by
    intro x i
    funext j
    simp only [hE, flipAt_apply]
    by_cases hj : j = e i
    · subst hj
      simp
    · have hne : e.symm j ≠ i := fun h => hj (by rw [← h, Equiv.apply_symm_apply])
      simp [hj, hne]
  obtain ⟨x', hx'A, hx'⟩ := huang_fin m (A.image E) (by
    rw [Finset.card_image_of_injective A E.injective]
    rw [hm] at hA
    simpa using hA)
  obtain ⟨x, hxA, hxx'⟩ := Finset.mem_image.mp hx'A
  refine ⟨x, hxA, ?_⟩
  have hcards : #{j ∈ (univ : Finset (Fin (m + 1))) | flipAt x' j ∈ A.image E}
      ≤ #{i ∈ (univ : Finset ι) | flipAt x i ∈ A} := by
    refine Finset.card_le_card_of_injOn (fun j => e.symm j) ?_ ?_
    · intro j hj
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hj ⊢
      have : flipAt x' j = E (flipAt x (e.symm j)) := by
        rw [hEflip, hxx', Equiv.apply_symm_apply]
      rw [this] at hj
      have := Finset.mem_image.mp hj
      obtain ⟨y, hy, hEy⟩ := this
      have : y = flipAt x (e.symm j) := E.injective hEy
      rwa [← this]
    · intro a _ b _ h
      exact e.symm.injective h
  have hcardsR : (#{j ∈ (univ : Finset (Fin (m + 1))) | flipAt x' j ∈ A.image E} : ℝ)
      ≤ (#{i ∈ (univ : Finset ι) | flipAt x i ∈ A} : ℝ) := by exact_mod_cast hcards
  refine le_trans ?_ hcardsR
  rw [hm]
  push_cast
  exact hx'

/-! ## The top-degree case -/

omit [Fintype ι] [DecidableEq ι] in
theorem chi_mul_self (S : Finset ι) (x : ι → Bool) : chi S x * chi S x = 1 := by
  rw [chi, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => by cases x i <;> norm_num [bsign]

omit [Fintype ι] [DecidableEq ι] in
theorem chi_eq_one_or_neg_one (S : Finset ι) (x : ι → Bool) : chi S x = 1 ∨ chi S x = -1 :=
  mul_self_eq_one_iff.mp (chi_mul_self S x)

theorem eq_neg_of_ne_of_sign {a c : ℝ} (ha : a = 1 ∨ a = -1) (hc : c = 1 ∨ c = -1)
    (h : ¬ a = c) : a = -c := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
  · exact absurd rfl h
  · norm_num
  · norm_num
  · exact absurd rfl h

theorem bsign_eq_one_or_neg_one (b : Bool) : bsign b = 1 ∨ bsign b = -1 := by
  cases b <;> norm_num [bsign]

/-- If a large set `A` of points is such that flipping a coordinate inside `A` always changes
the value of `f`, then `f` has sensitivity at least `√(card ι)`. -/
theorem sqrt_card_le_sensitivity_of_big_set (f : (ι → Bool) → Bool) (A : Finset (ι → Bool))
    (hA : ∀ x ∈ A, ∀ i : ι, flipAt x i ∈ A → f (flipAt x i) ≠ f x)
    (hbig : 2 ^ (Fintype.card ι - 1) < A.card) :
    Real.sqrt (Fintype.card ι) ≤ sensitivity f := by
  obtain ⟨x, hx, hcard⟩ := huang_flip A hbig
  refine hcard.trans ?_
  have hsub : {i ∈ (univ : Finset ι) | flipAt x i ∈ A} ⊆ {i ∈ (univ : Finset ι) | f (flipAt x i) ≠ f x} := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hA x hx i hi
  have h1 : (#{i ∈ (univ : Finset ι) | flipAt x i ∈ A} : ℝ) ≤ (sensitivityAt f x : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine h1.trans ?_
  exact_mod_cast Finset.le_sup (f := fun z => sensitivityAt f z) (mem_univ x)

theorem sqrt_card_le_sensitivity_of_top_coeff (f : (ι → Bool) → Bool)
    (hf : fourierCoeff f (univ : Finset ι) ≠ 0) :
    Real.sqrt (Fintype.card ι) ≤ sensitivity f := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · rw [hn]
    simp
  set A : Finset (ι → Bool) :=
    {x ∈ (univ : Finset (ι → Bool)) | bsign (f x) = chi (univ : Finset ι) x} with hAdef
  set B : Finset (ι → Bool) :=
    {x ∈ (univ : Finset (ι → Bool)) | ¬ bsign (f x) = chi (univ : Finset ι) x} with hBdef
  -- the two sets partition the cube
  have hpart : A.card + B.card = 2 ^ Fintype.card ι := by
    rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not]
    simp [Finset.card_univ]
  -- the Fourier coefficient computes the difference of their sizes
  have hsum : ∑ x : ι → Bool, bsign (f x) * chi (univ : Finset ι) x
      = (A.card : ℝ) - (B.card : ℝ) := by
    have hterm : ∀ x : ι → Bool, bsign (f x) * chi (univ : Finset ι) x
        = if bsign (f x) = chi (univ : Finset ι) x then (1 : ℝ) else -1 := by
      intro x
      rcases bsign_eq_one_or_neg_one (f x) with ha | ha <;>
        rcases chi_eq_one_or_neg_one (univ : Finset ι) x with hc | hc <;>
          rw [ha, hc] <;> norm_num
    rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_ite]
    simp [hAdef, hBdef, sub_eq_add_neg]
  have hne : A.card ≠ B.card := by
    intro h
    apply hf
    rw [fourierCoeff, hsum, h]
    simp
  -- hence one of them contains more than half of the cube
  have hhalf : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    conv_lhs => rw [show Fintype.card ι = (Fintype.card ι - 1) + 1 by omega]
    ring
  have hcase : 2 ^ (Fintype.card ι - 1) < A.card ∨ 2 ^ (Fintype.card ι - 1) < B.card := by
    rw [hhalf] at hpart
    omega
  rcases hcase with hbig | hbig
  · refine sqrt_card_le_sensitivity_of_big_set f A ?_ hbig
    intro x hx i hxi
    rw [hAdef, mem_filter] at hx hxi
    have h1 : bsign (f (flipAt x i)) = -bsign (f x) := by
      rw [hxi.2, chi_flipAt, hx.2]
    intro hcon
    have h2 : bsign (f (flipAt x i)) = bsign (f x) := by rw [hcon]
    rw [h1] at h2
    exact bsign_ne_zero (f x) (by linarith)
  · refine sqrt_card_le_sensitivity_of_big_set f B ?_ hbig
    intro x hx i hxi
    rw [hBdef, mem_filter] at hx hxi
    have hx2 : bsign (f x) = -chi (univ : Finset ι) x :=
      eq_neg_of_ne_of_sign (bsign_eq_one_or_neg_one _) (chi_eq_one_or_neg_one _ _) hx.2
    have hxi2 : bsign (f (flipAt x i)) = -chi (univ : Finset ι) (flipAt x i) :=
      eq_neg_of_ne_of_sign (bsign_eq_one_or_neg_one _) (chi_eq_one_or_neg_one _ _) hxi.2
    have h1 : bsign (f (flipAt x i)) = -bsign (f x) := by
      rw [hxi2, chi_flipAt, hx2]
    intro hcon
    have h2 : bsign (f (flipAt x i)) = bsign (f x) := by rw [hcon]
    rw [h1] at h2
    exact bsign_ne_zero (f x) (by linarith)

/-! ## Restrictions -/

/-- Merge a partial assignment on `S` with a partial assignment off `S`. -/
def merge (S : Finset ι) (y : {i // i ∈ S} → Bool) (r : {i // i ∉ S} → Bool) : ι → Bool :=
  fun i => if h : i ∈ S then y ⟨i, h⟩ else r ⟨i, h⟩

/-- The restriction of `f` obtained by fixing the variables outside `S` according to `r`. -/
def restrict (f : (ι → Bool) → Bool) (S : Finset ι) (r : {i // i ∉ S} → Bool) :
    ({i // i ∈ S} → Bool) → Bool := fun y => f (merge S y r)

omit [Fintype ι] in
theorem merge_apply_mem (S : Finset ι) (y : {i // i ∈ S} → Bool) (r : {i // i ∉ S} → Bool)
    (i : ι) (h : i ∈ S) : merge S y r i = y ⟨i, h⟩ := by simp [merge, h]

omit [Fintype ι] in
theorem merge_flipAt (S : Finset ι) (y : {i // i ∈ S} → Bool) (r : {i // i ∉ S} → Bool)
    (j : {i // i ∈ S}) : merge S (flipAt y j) r = flipAt (merge S y r) (j : ι) := by
  funext i
  by_cases h : i ∈ S
  · rw [merge_apply_mem S _ r i h, flipAt_apply, flipAt_apply, merge_apply_mem S y r i h]
    by_cases hij : i = (j : ι)
    · have : (⟨i, h⟩ : {i // i ∈ S}) = j := Subtype.ext hij
      simp [hij, merge_apply_mem S y r (j : ι) j.2]
    · have : (⟨i, h⟩ : {i // i ∈ S}) ≠ j := fun hh => hij (congrArg Subtype.val hh)
      simp [this, hij]
  · have hij : i ≠ (j : ι) := fun hh => h (hh ▸ j.2)
    rw [flipAt_of_ne hij]
    simp [merge, h]

theorem sensitivityAt_restrict_le (f : (ι → Bool) → Bool) (S : Finset ι)
    (r : {i // i ∉ S} → Bool) (y : {i // i ∈ S} → Bool) :
    sensitivityAt (restrict f S r) y ≤ sensitivityAt f (merge S y r) := by
  refine Finset.card_le_card_of_injOn (fun j => (j : ι)) ?_ ?_
  · intro j hj
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hj ⊢
    rw [← merge_flipAt]
    exact hj
  · intro a _ b _ h
    exact Subtype.ext h

theorem sensitivity_restrict_le (f : (ι → Bool) → Bool) (S : Finset ι)
    (r : {i // i ∉ S} → Bool) : sensitivity (restrict f S r) ≤ sensitivity f := by
  refine Finset.sup_le ?_
  intro y _
  exact le_trans (sensitivityAt_restrict_le f S r y)
    (Finset.le_sup (f := fun x => sensitivityAt f x) (mem_univ (merge S y r)))

omit [Fintype ι] in
theorem chi_merge (S : Finset ι) (y : {i // i ∈ S} → Bool) (r : {i // i ∉ S} → Bool) :
    chi S (merge S y r) = chi (univ : Finset {i // i ∈ S}) y := by
  rw [chi, chi, ← Finset.prod_coe_sort S (fun i => bsign (merge S y r i))]
  exact Finset.prod_congr rfl fun j _ => by rw [merge_apply_mem S y r (j : ι) j.2]

omit [Fintype ι] in
theorem merge_eq_symm (S : Finset ι) (y : {i // i ∈ S} → Bool) (r : {i // i ∉ S} → Bool) :
    merge S y r = (Equiv.piEquivPiSubtypeProd (· ∈ S) (fun _ => Bool)).symm (y, r) := rfl

/-- Averaging the top Fourier coefficients of all restrictions off `S` recovers the Fourier
coefficient of `f` at `S`. -/
theorem sum_restrict_top (f : (ι → Bool) → Bool) (S : Finset ι) :
    ∑ r : {i // i ∉ S} → Bool, ∑ y : {i // i ∈ S} → Bool,
        bsign (restrict f S r y) * chi (univ : Finset {i // i ∈ S}) y
      = ∑ z : ι → Bool, bsign (f z) * chi S z := by
  have key : ∑ p : ({i // i ∈ S} → Bool) × ({i // i ∉ S} → Bool),
      bsign (restrict f S p.2 p.1) * chi (univ : Finset {i // i ∈ S}) p.1
        = ∑ z : ι → Bool, bsign (f z) * chi S z := by
    refine Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ S) (fun _ => Bool)).symm _ _ ?_
    rintro ⟨y, r⟩
    rw [← merge_eq_symm, chi_merge]
    rfl
  rw [Fintype.sum_prod_type] at key
  rw [Finset.sum_comm]
  exact key

theorem exists_restrict_top_coeff_ne_zero (f : (ι → Bool) → Bool) (S : Finset ι)
    (hS : fourierCoeff f S ≠ 0) :
    ∃ r : {i // i ∉ S} → Bool, fourierCoeff (restrict f S r) (univ : Finset {i // i ∈ S}) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ r : {i // i ∉ S} → Bool,
      ∑ y : {i // i ∈ S} → Bool,
        bsign (restrict f S r y) * chi (univ : Finset {i // i ∈ S}) y = 0 := by
    intro r
    have := hcon r
    rw [fourierCoeff, mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (by positivity)
    · exact h
  have hsum : ∑ z : ι → Bool, bsign (f z) * chi S z = 0 := by
    rw [← sum_restrict_top f S]
    exact Finset.sum_eq_zero fun r _ => hzero r
  rw [fourierCoeff, hsum, mul_zero] at hS
  exact hS rfl

/-! ## Justification of the definition of degree: the Fourier expansion

We check that `degree` really is the degree of the multilinear polynomial representing `f`:
the `±1` encoding `bsign ∘ f` of `f` is the sum of `fourierCoeff f S * chi S` over all `S`,
and only sets `S` of size at most `degree f` contribute. -/

omit [Fintype ι] [DecidableEq ι] in
theorem chi_mul_chi (S : Finset ι) (x y : ι → Bool) :
    chi S x * chi S y = ∏ i ∈ S, (bsign (x i) * bsign (y i)) := by
  rw [chi, chi, Finset.prod_mul_distrib]

/-- Orthogonality of the Fourier–Walsh characters. -/
theorem sum_chi_mul_chi (x y : ι → Bool) :
    ∑ S : Finset ι, chi S x * chi S y = if x = y then (2 ^ Fintype.card ι : ℝ) else 0 := by
  have key : ∏ i : ι, (bsign (x i) * bsign (y i) + 1) = ∑ S : Finset ι, chi S x * chi S y := by
    rw [Finset.prod_add, Finset.powerset_univ]
    exact Finset.sum_congr rfl fun t _ => by
      rw [chi_mul_chi, Finset.prod_const_one, mul_one]
  rw [← key]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have : ∀ i ∈ (univ : Finset ι), bsign (x i) * bsign (x i) + 1 = (2 : ℝ) := by
      intro i _
      cases x i <;> norm_num [bsign]
    rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_univ]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    refine Finset.prod_eq_zero (mem_univ i) ?_
    cases hx : x i <;> cases hy : y i <;> simp_all [bsign]

/-- The Fourier expansion: the `±1` encoding of `f` is recovered from its Fourier
coefficients. -/
theorem fourier_expansion (f : (ι → Bool) → Bool) (x : ι → Bool) :
    ∑ S : Finset ι, fourierCoeff f S * chi S x = bsign (f x) := by
  have h1 : ∀ S : Finset ι, fourierCoeff f S * chi S x
      = (2 ^ Fintype.card ι : ℝ)⁻¹ * ∑ y : ι → Bool, bsign (f y) * (chi S y * chi S x) := by
    intro S
    rw [fourierCoeff, mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl fun S _ => h1 S, ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ y : ι → Bool, ∑ S : Finset ι, bsign (f y) * (chi S y * chi S x)
      = bsign (f y) * (if y = x then (2 ^ Fintype.card ι : ℝ) else 0) := by
    intro y
    rw [← Finset.mul_sum, sum_chi_mul_chi]
  rw [Finset.sum_congr rfl fun y _ => h2 y]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' univ x (fun y => bsign (f y) * (2 ^ Fintype.card ι : ℝ))]
  rw [if_pos (mem_univ x)]
  field_simp

/-- Only sets of size at most `degree f` occur in the Fourier expansion of `f`. -/
theorem fourierCoeff_eq_zero_of_degree_lt (f : (ι → Bool) → Bool) (S : Finset ι)
    (h : degree f < S.card) : fourierCoeff f S = 0 := by
  by_contra hne
  have hmem : S ∈ {T ∈ (univ : Finset (Finset ι)) | fourierCoeff f T ≠ 0} := by
    simp [hne]
  exact absurd (Finset.le_sup (f := Finset.card) hmem) (by simpa [degree] using Nat.not_le.mpr h)

/-! ## Huang's sensitivity theorem -/

/-- **Huang's sensitivity theorem**: for every Boolean function on a finite set of
variables, the Fourier degree is at most the square of the sensitivity. -/
theorem huang_sensitivity (f : (ι → Bool) → Bool) : degree f ≤ (sensitivity f) ^ 2 := by
  rcases Finset.eq_empty_or_nonempty
      {S ∈ (univ : Finset (Finset ι)) | fourierCoeff f S ≠ 0} with h | h
  · simp [degree, h]
  · obtain ⟨S, hS, hsup⟩ := Finset.exists_mem_eq_sup _ h Finset.card
    rw [Finset.mem_filter] at hS
    obtain ⟨r, hr⟩ := exists_restrict_top_coeff_ne_zero f S hS.2
    have h1 := sqrt_card_le_sensitivity_of_top_coeff (restrict f S r) hr
    have h2 := sensitivity_restrict_le f S r
    rw [Fintype.card_coe S] at h1
    have h3 : Real.sqrt (S.card : ℝ) ≤ (sensitivity f : ℝ) :=
      le_trans h1 (by exact_mod_cast h2)
    have h4 : (S.card : ℝ) ≤ ((sensitivity f : ℝ)) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (S.card : ℝ) by positivity),
        Real.sqrt_nonneg (S.card : ℝ)]
    have hdeg : degree f = S.card := by rw [degree, hsup]
    rw [hdeg]
    exact_mod_cast h4

/-! ## Sanity checks: the definitions are non-degenerate and the bound is attained -/

/-- A Boolean function of degree `0` is constant. -/
theorem const_of_degree_eq_zero (f : (ι → Bool) → Bool) (h : degree f = 0) (x y : ι → Bool) :
    f x = f y := by
  have hx : ∀ z : ι → Bool, bsign (f z) = fourierCoeff f ∅ := by
    intro z
    rw [← fourier_expansion f z, Finset.sum_eq_single (∅ : Finset ι)]
    · simp [chi]
    · intro S _ hS
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      rw [fourierCoeff_eq_zero_of_degree_lt f S (by omega), zero_mul]
    · intro hcon
      exact absurd (mem_univ _) hcon
  rw [← bsign_eq_bsign_iff, hx x, hx y]

/-- The sensitivity of a dictator function is `1`. -/
theorem sensitivityAt_dictator (i : ι) (x : ι → Bool) :
    sensitivityAt (fun z : ι → Bool => z i) x = 1 := by
  have hset : {j ∈ (univ : Finset ι) | (flipAt x j) i ≠ x i} = {i} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hj
      by_contra hne
      exact hj (flipAt_of_ne (Ne.symm hne))
    · rintro rfl
      simp
  rw [sensitivityAt, hset, Finset.card_singleton]

theorem sensitivity_dictator (i : ι) : sensitivity (fun z : ι → Bool => z i) = 1 := by
  rw [sensitivity]
  rw [Finset.sup_congr rfl fun x _ => sensitivityAt_dictator i x]
  exact Finset.sup_const Finset.univ_nonempty 1

/-- The degree of a dictator function is `1`; in particular the bound
`degree f ≤ (sensitivity f)^2` of `Frontier.huang_sensitivity` is attained. -/
theorem degree_dictator (i : ι) : degree (fun z : ι → Bool => z i) = 1 := by
  have hle : degree (fun z : ι → Bool => z i) ≤ 1 := by
    have := huang_sensitivity (fun z : ι → Bool => z i)
    rwa [sensitivity_dictator, one_pow] at this
  have hpos : degree (fun z : ι → Bool => z i) ≠ 0 := by
    intro h0
    have := const_of_degree_eq_zero _ h0 (fun _ => false) (fun _ => true)
    simp at this
  omega

end Frontier

