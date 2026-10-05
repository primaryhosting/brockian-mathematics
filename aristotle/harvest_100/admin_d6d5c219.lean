/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℤ :=
  ∏ i ∈ S, (if x i then (-1 : ℤ) else 1)

/-- The (unnormalized) Fourier coefficient of `f` at `S`, i.e. `∑_x (-1)^{f x} χ_S(x)`.
It is `2^n` times the usual Fourier coefficient of the `±1`-valued version of `f`. -/
def fourierCoeff {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℤ :=
  ∑ x : Fin n → Bool, (if f x then (-1 : ℤ) else 1) * chi S x

/-- The degree of a Boolean function: the largest size of a set carrying a nonzero
Fourier coefficient, i.e. the degree of the unique multilinear polynomial
representing `f`. -/
def degree {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => fourierCoeff f S ≠ 0)).sup Finset.card

/-- Flip the `i`-th coordinate of `x`. -/
def flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

/-- The local sensitivity of `f` at `x`: the number of coordinates whose flip changes
the value of `f`. -/
def sensAt {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => f (flipAt x i) ≠ f x)).card

/-- The sensitivity of `f`: the maximum of its local sensitivities. -/
def sens {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  (Finset.univ : Finset (Fin n → Bool)).sup (sensAt f)

/-! ## Elementary facts about coordinate flips -/

lemma flipAt_self {n : ℕ} (x : Fin n → Bool) (i : Fin n) : flipAt x i i = !x i := by
  simp [flipAt]

lemma flipAt_ne {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (h : j ≠ i) : flipAt x i j = x j := by
  simp [flipAt, Function.update_of_ne h]

lemma flipAt_flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) : flipAt (flipAt x i) i = x := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [flipAt_self]
  · simp [flipAt_ne _ hj]

lemma flipAt_comm {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    flipAt (flipAt x i) j = flipAt (flipAt x j) i := by
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [flipAt_self, flipAt_ne]

/-- Connectivity of the hypercube: a predicate preserved by all flips in a set `S` of
coordinates propagates between any two points differing only inside `S`. -/
lemma cube_connected {n : ℕ} {P : (Fin n → Bool) → Prop} {S : Finset (Fin n)}
    (hstep : ∀ x j, j ∈ S → P x → P (flipAt x j)) :
    ∀ x y, (∀ i, x i ≠ y i → i ∈ S) → P x → P y := by
  have key : ∀ (d : ℕ) (x y : Fin n → Bool),
      ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card = d →
      (∀ i, x i ≠ y i → i ∈ S) → P x → P y := by
    intro d
    induction d with
    | zero =>
      intro x y hd _ hP
      have hxy : ∀ i, x i = y i := by
        intro i
        by_contra hi
        have hmem : i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i) := by
          simp [hi]
        rw [Finset.card_eq_zero.1 hd] at hmem
        simp at hmem
      rwa [← funext hxy]
    | succ d ih =>
      intro x y hd hS hP
      obtain ⟨i0, hi0⟩ : ∃ i0, x i0 ≠ y i0 := by
        by_contra hcon
        push_neg at hcon
        have hemp : (Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i) = ∅ := by
          simp [hcon]
        rw [hemp] at hd
        simp at hd
      have hxy : flipAt x i0 i0 = y i0 := by
        rw [flipAt_self]
        revert hi0; cases x i0 <;> cases y i0 <;> simp
      have hcard : ((Finset.univ : Finset (Fin n)).filter (fun i => flipAt x i0 i ≠ y i))
          = ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).erase i0 := by
        ext j
        by_cases hj : j = i0
        · subst hj; simp [hxy]
        · simp [hj, flipAt_ne x hj]
      refine ih (flipAt x i0) y ?_ ?_ (hstep x i0 (hS i0 hi0) hP)
      · rw [hcard, Finset.card_erase_of_mem (by simp [hi0]), hd]
        rfl
      · intro i hi
        apply hS
        by_cases hij : i = i0
        · subst hij; exact hi0
        · rwa [flipAt_ne x hij] at hi
  intro x y hS hP
  exact key _ x y rfl hS hP

/-- If no single coordinate flip ever changes the value of `f`, then `f` is constant. -/
lemma const_of_local {n : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ∀ x i, f (flipAt x i) = f x) : ∀ x y, f x = f y := by
  intro x y
  refine cube_connected (P := fun z => f x = f z) (S := Finset.univ) ?_ x y (by simp) rfl
  intro z j _ hz
  show f x = f (flipAt z j)
  rw [h z j]
  exact hz

/-! ## Character sums -/

/-- Orthogonality of characters, summed over the sets: `∑_S χ_S(x) χ_S(y)` is `2^n`
if `x = y` and `0` otherwise. -/
lemma sum_chi_mul_chi {n : ℕ} (x y : Fin n → Bool) :
    (∑ S : Finset (Fin n), chi S x * chi S y) = if x = y then (2 : ℤ) ^ n else 0 := by
  have key : ∀ S : Finset (Fin n), chi S x * chi S y
      = ∏ i ∈ S, ((if x i then (-1 : ℤ) else 1) * (if y i then (-1 : ℤ) else 1)) := by
    intro S
    rw [chi, chi, ← Finset.prod_mul_distrib]
  simp only [key]
  have h2 : ∏ i : Fin n, (((if x i then (-1 : ℤ) else 1) * (if y i then (-1 : ℤ) else 1)) + 1)
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ S, ((if x i then (-1 : ℤ) else 1) * (if y i then (-1 : ℤ) else 1)))
          * ∏ _i ∈ Finset.univ \ S, (1 : ℤ) := Finset.prod_add _ _ _
  simp only [Finset.prod_const_one, mul_one, Finset.powerset_univ] at h2
  rw [← h2]
  by_cases hxy : x = y
  · subst hxy
    have hall : ∀ i : Fin n,
        (((if x i then (-1 : ℤ) else 1) * (if x i then (-1 : ℤ) else 1)) + 1) = 2 := by
      intro i; cases x i <;> norm_num
    rw [Finset.prod_congr rfl (fun i _ => hall i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, if_pos rfl]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      exact hxy (funext fun i => not_not.1 (fun hh => h ⟨i, hh⟩))
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    revert hi
    cases hx : x i <;> cases hy : y i <;> simp

/-- Summed over the cube, a character is `2^n` for `S = ∅` and `0` otherwise. -/
lemma sum_chi {n : ℕ} (S : Finset (Fin n)) :
    (∑ x : Fin n → Bool, chi S x) = if S = ∅ then (2 : ℤ) ^ n else 0 := by
  have hchi : ∀ x : Fin n → Bool,
      chi S x = ∏ i : Fin n, (if i ∈ S then (if x i then (-1 : ℤ) else 1) else 1) := by
    intro x
    rw [Finset.prod_ite_mem, Finset.univ_inter, chi]
  simp only [hchi]
  rw [← Fintype.piFinset_univ (α := Fin n) (β := fun _ => Bool),
    ← Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
      (fun i b => if i ∈ S then (if b then (-1 : ℤ) else 1) else 1)]
  have hb : ∀ i : Fin n,
      (∑ b : Bool, if i ∈ S then (if b then (-1 : ℤ) else 1) else 1)
        = if i ∈ S then (0 : ℤ) else 2 := by
    intro i
    by_cases h : i ∈ S <;> simp [h]
  simp only [hb]
  by_cases hS : S = ∅
  · subst hS
    simp
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hS
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma chi_empty {n : ℕ} (x : Fin n → Bool) : chi (∅ : Finset (Fin n)) x = 1 := by
  simp [chi]

lemma chi_flipAt_of_notMem {n : ℕ} {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S)
    (x : Fin n → Bool) : chi S (flipAt x i) = chi S x :=
  Finset.prod_congr rfl fun j hj => by rw [flipAt_ne x (by rintro rfl; exact hi hj)]

lemma chi_flipAt_of_mem {n : ℕ} {S : Finset (Fin n)} {i : Fin n} (hi : i ∈ S)
    (x : Fin n → Bool) : chi S (flipAt x i) = - chi S x := by
  rw [chi, chi, ← Finset.prod_erase_mul _ _ hi, ← Finset.prod_erase_mul _ _ hi]
  have h1 : ∏ j ∈ S.erase i, (if flipAt x i j then (-1 : ℤ) else 1)
      = ∏ j ∈ S.erase i, (if x j then (-1 : ℤ) else 1) :=
    Finset.prod_congr rfl fun j hj => by rw [flipAt_ne x (Finset.ne_of_mem_erase hj)]
  rw [h1, flipAt_self]
  cases x i <;> ring_nf <;> simp

/-- Fourier inversion: `∑_S f̂(S) χ_S(x) = 2^n (-1)^{f x}`. -/
lemma sum_coeff_mul_chi {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (∑ S : Finset (Fin n), fourierCoeff f S * chi S x)
      = 2 ^ n * (if f x then (-1 : ℤ) else 1) := by
  have hswap : (∑ S : Finset (Fin n), fourierCoeff f S * chi S x)
      = ∑ y : Fin n → Bool, (if f y then (-1 : ℤ) else 1) *
          (∑ S : Finset (Fin n), chi S y * chi S x) := by
    simp only [fourierCoeff, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hswap]
  simp only [sum_chi_mul_chi]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- A Fourier coefficient at a set containing a coordinate that `f` does not depend on
vanishes. -/
lemma coeff_eq_zero_of_invariant {n : ℕ} {f : (Fin n → Bool) → Bool} {k : Fin n}
    (hinv : ∀ x, f (flipAt x k) = f x) {S : Finset (Fin n)} (hk : k ∈ S) :
    fourierCoeff f S = 0 := by
  have hbij : (∑ x : Fin n → Bool, (if f x then (-1 : ℤ) else 1) * chi S x)
      = ∑ x : Fin n → Bool, (if f (flipAt x k) then (-1 : ℤ) else 1) * chi S (flipAt x k) := by
    refine (Fintype.sum_equiv (Function.Involutive.toPerm (fun x => flipAt x k)
      (fun x => flipAt_flipAt x k)) _ _ ?_).symm
    intro x
    rfl
  have hneg : fourierCoeff f S = - fourierCoeff f S := by
    conv_lhs => rw [fourierCoeff, hbij]
    simp only [hinv, chi_flipAt_of_mem hk, mul_neg, Finset.sum_neg_distrib]
    rw [fourierCoeff]
  linarith

/-! ## Degree zero and sensitivity zero both characterize constant functions -/

lemma sens_eq_zero_iff_const {n : ℕ} (f : (Fin n → Bool) → Bool) :
    sens f = 0 ↔ ∀ x y, f x = f y := by
  constructor
  · intro h
    apply const_of_local
    intro x i
    have hx : sensAt f x = 0 := by
      have hle : sensAt f x ≤ sens f := Finset.le_sup (Finset.mem_univ x)
      omega
    by_contra hne
    have hmem : i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => f (flipAt x i) ≠ f x) := by
      simp [hne]
    rw [Finset.card_eq_zero.1 hx] at hmem
    simp at hmem
  · intro h
    apply Nat.le_zero.1
    apply Finset.sup_le
    intro x _
    simp only [sensAt, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    simp [h (flipAt x i) x]

lemma degree_eq_zero_iff_const {n : ℕ} (f : (Fin n → Bool) → Bool) :
    degree f = 0 ↔ ∀ x y, f x = f y := by
  constructor
  · intro h x y
    have hzero : ∀ S : Finset (Fin n), S ≠ ∅ → fourierCoeff f S = 0 := by
      intro S hS
      by_contra hc
      have hmem : S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun S => fourierCoeff f S ≠ 0) := by simp [hc]
      have hcard : S.card ≤ degree f := Finset.le_sup hmem
      rw [h, Nat.le_zero, Finset.card_eq_zero] at hcard
      exact hS hcard
    have hval : ∀ z : Fin n → Bool,
        2 ^ n * (if f z then (-1 : ℤ) else 1) = fourierCoeff f ∅ := by
      intro z
      rw [← sum_coeff_mul_chi f z, Finset.sum_eq_single (∅ : Finset (Fin n))]
      · rw [chi_empty, mul_one]
      · intro S _ hS
        rw [hzero S hS, zero_mul]
      · intro hc
        exact absurd (Finset.mem_univ (∅ : Finset (Fin n))) hc
    have h2 : (2 : ℤ) ^ n * (if f x then (-1 : ℤ) else 1)
        = 2 ^ n * (if f y then (-1 : ℤ) else 1) := by rw [hval x, hval y]
    have hpow : (0 : ℤ) < 2 ^ n := by positivity
    have hcancel := mul_left_cancel₀ (ne_of_gt hpow) h2
    revert hcancel
    cases hx : f x <;> cases hy : f y <;> simp
  · intro h
    apply Nat.le_zero.1
    apply Finset.sup_le
    intro S hS
    simp only [Finset.mem_filter] at hS
    have hempty : S = ∅ := by
      by_contra hne
      apply hS.2
      have hconst : ∀ y : Fin n → Bool, (if f y then (-1 : ℤ) else 1)
          = (if f (fun _ => false) then (-1 : ℤ) else 1) := by
        intro y; rw [h y (fun _ => false)]
      simp only [fourierCoeff, hconst, ← Finset.mul_sum, sum_chi, if_neg hne, mul_zero]
    simp [hempty]

/-! ## Degree at most one and sensitivity at most one -/

lemma coeff_eq_zero_of_two_le_card {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    {S : Finset (Fin n)} (hS : 2 ≤ S.card) : fourierCoeff f S = 0 := by
  by_contra hc
  have hmem : S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => fourierCoeff f S ≠ 0) := by simp [hc]
  have hle : S.card ≤ degree f := Finset.le_sup hmem
  omega

/-- For a function of degree at most one, flipping a coordinate changes the `±1`-valued
version of `f` by exactly twice the corresponding singleton Fourier coefficient. -/
lemma flip_diff {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    (x : Fin n → Bool) (i : Fin n) :
    2 ^ n * ((if f x then (-1 : ℤ) else 1) - (if f (flipAt x i) then (-1 : ℤ) else 1))
      = 2 * fourierCoeff f {i} * (if x i then (-1 : ℤ) else 1) := by
  rw [mul_sub, ← sum_coeff_mul_chi f x, ← sum_coeff_mul_chi f (flipAt x i),
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single ({i} : Finset (Fin n))]
  · rw [chi_flipAt_of_mem (by simp) x, chi, Finset.prod_singleton]
    ring
  · intro S _ hS
    rcases Nat.lt_or_ge S.card 2 with h2 | h2
    · have hcases : S.card = 0 ∨ S.card = 1 := by omega
      rcases hcases with h | h
      · rw [Finset.card_eq_zero.1 h]
        simp [chi]
      · obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h
        subst hj
        have hij : i ∉ ({j} : Finset (Fin n)) := by
          simp only [Finset.mem_singleton]
          rintro rfl
          exact hS rfl
        rw [chi_flipAt_of_notMem hij x]
        ring
    · rw [coeff_eq_zero_of_two_le_card hdeg h2]; ring
  · intro hc
    exact absurd (Finset.mem_univ _) hc

lemma coeff_singleton_mul_sign {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    {x : Fin n → Bool} {i : Fin n} (hne : f (flipAt x i) ≠ f x) :
    fourierCoeff f {i} * (if x i then (-1 : ℤ) else 1)
      = 2 ^ n * (if f x then (-1 : ℤ) else 1) := by
  have hg : (if f (flipAt x i) then (-1 : ℤ) else 1) = -(if f x then (-1 : ℤ) else 1) := by
    revert hne; cases f x <;> cases f (flipAt x i) <;> simp
  have h := flip_diff hdeg x i
  rw [hg] at h
  refine mul_left_cancel₀ two_ne_zero ?_
  linarith [h]

lemma coeff_singleton_ne_zero {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    {x : Fin n → Bool} {i : Fin n} (hne : f (flipAt x i) ≠ f x) : fourierCoeff f {i} ≠ 0 := by
  intro h0
  have h := coeff_singleton_mul_sign hdeg hne
  rw [h0, zero_mul] at h
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  cases f x <;> simp at h <;> omega

lemma sensitive_of_coeff {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    {i : Fin n} (hc : fourierCoeff f {i} ≠ 0) (x : Fin n → Bool) : f (flipAt x i) ≠ f x := by
  intro heq
  have h := flip_diff hdeg x i
  rw [heq, sub_self, mul_zero] at h
  have hs : (if x i then (-1 : ℤ) else 1) ≠ 0 := by cases x i <;> norm_num
  rcases mul_eq_zero.1 h.symm with h1 | h2
  · rcases mul_eq_zero.1 h1 with h3 | h4
    · norm_num at h3
    · exact hc h4
  · exact hs h2

/-- A Boolean function of degree at most one has sensitivity at most one: it is constant
or a (possibly negated) dictator. -/
lemma sens_le_one_of_degree_le_one {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1) :
    sens f ≤ 1 := by
  apply Finset.sup_le
  intro x _
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  by_contra hab
  have hca := coeff_singleton_ne_zero hdeg ha.2
  have hcb := coeff_singleton_ne_zero hdeg hb.2
  set y := flipAt x b with hy
  have hya : f (flipAt y a) ≠ f y := sensitive_of_coeff hdeg hca y
  have hyb : f (flipAt y b) ≠ f y := sensitive_of_coeff hdeg hcb y
  have e1 := coeff_singleton_mul_sign hdeg ha.2
  have e2 := coeff_singleton_mul_sign hdeg hb.2
  have e3 := coeff_singleton_mul_sign hdeg hya
  have e4 := coeff_singleton_mul_sign hdeg hyb
  have hya' : y a = x a := flipAt_ne x hab
  have hyb' : y b = !x b := flipAt_self x b
  rw [hya'] at e3
  rw [hyb'] at e4
  have hsgn : (if (!x b) then (-1 : ℤ) else 1) = -(if x b then (-1 : ℤ) else 1) := by
    cases x b <;> simp
  rw [hsgn] at e4
  have hgx : (2 : ℤ) ^ n * (if f x then (-1 : ℤ) else 1)
      = 2 ^ n * (if f y then (-1 : ℤ) else 1) := by
    rw [← e1, ← e3]
  have hgy : (2 : ℤ) ^ n * (if f y then (-1 : ℤ) else 1)
      = -(2 ^ n * (if f x then (-1 : ℤ) else 1)) := by
    rw [← e4, ← e2]; ring
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  rw [hgx] at hgy
  cases f y <;> simp at hgy <;> omega

/-- A Boolean function of sensitivity at most one has degree at most one. -/
lemma degree_le_one_of_sens_le_one {n : ℕ} {f : (Fin n → Bool) → Bool} (hsens : sens f ≤ 1) :
    degree f ≤ 1 := by
  have hsx : ∀ x, sensAt f x ≤ 1 := fun x =>
    le_trans (Finset.le_sup (f := sensAt f) (Finset.mem_univ x)) hsens
  by_cases hconst : ∀ x y, f x = f y
  · have h0 : degree f = 0 := (degree_eq_zero_iff_const f).2 hconst
    omega
  · obtain ⟨x0, i0, hx0⟩ : ∃ x i, f (flipAt x i) ≠ f x := by
      by_contra hc
      push_neg at hc
      exact hconst (const_of_local hc)
    have hstep : ∀ z j, j ∈ (Finset.univ : Finset (Fin n)) →
        (f (flipAt z i0) ≠ f z) → (f (flipAt (flipAt z j) i0) ≠ f (flipAt z j)) := by
      intro z j _ hz
      by_cases hj : j = i0
      · subst hj
        rw [flipAt_flipAt]
        exact fun h => hz h.symm
      · have h1 : f (flipAt z j) = f z := by
          by_contra hh
          exact hj (Finset.card_le_one.1 (hsx z) j (by simp [hh]) i0 (by simp [hz]))
        have hz' : f (flipAt (flipAt z i0) i0) ≠ f (flipAt z i0) := by
          rw [flipAt_flipAt]
          exact fun h => hz h.symm
        have h2 : f (flipAt (flipAt z i0) j) = f (flipAt z i0) := by
          by_contra hh
          exact hj (Finset.card_le_one.1 (hsx (flipAt z i0)) j (by simp [hh]) i0 (by simp [hz']))
        rw [flipAt_comm, h2, h1]
        exact hz
    have hall : ∀ x, f (flipAt x i0) ≠ f x := fun x =>
      cube_connected (P := fun z => f (flipAt z i0) ≠ f z) hstep x0 x (by simp) hx0
    have hinv : ∀ k, k ≠ i0 → ∀ x, f (flipAt x k) = f x := by
      intro k hk x
      by_contra hh
      exact hk (Finset.card_le_one.1 (hsx x) k (by simp [hh]) i0 (by simp [hall x]))
    apply Finset.sup_le
    intro S hS
    simp only [Finset.mem_filter] at hS
    apply Finset.card_le_one.2
    intro a ha b hb
    have hkey : ∀ k ∈ S, k = i0 := by
      intro k hk
      by_contra hne
      exact hS.2 (coeff_eq_zero_of_invariant (hinv k hne) hk)
    rw [hkey a ha, hkey b hb]

/-! ## The verified small cases -/

/-- Huang's inequality `deg f ≤ s(f)^2`, together with `s(f) ≤ deg(f)^2`, verified
for every Boolean function of three variables. -/
lemma huang_three_vars (t : Bool → Bool → Bool → Bool) :
    degree (fun x : Fin 3 → Bool => t (x 0) (x 1) (x 2)) ≤
        sens (fun x : Fin 3 → Bool => t (x 0) (x 1) (x 2)) ^ 2 ∧
      sens (fun x : Fin 3 → Bool => t (x 0) (x 1) (x 2)) ≤
        degree (fun x : Fin 3 → Bool => t (x 0) (x 1) (x 2)) ^ 2 := by
  revert t
  decide

/-- **Huang's sensitivity theorem, base cases.**

Sensitivity and degree of Boolean functions are polynomially related.  We prove:

* (general `n`) the base cases of the relation: the sensitivity of `f` is `0` exactly
  when its degree is `0` (exactly when `f` is constant), and the sensitivity of `f` is
  at most `1` exactly when its degree is at most `1`;
* (`n = 3`) the full two-sided polynomial relation `deg f ≤ s(f)^2` (Huang's
  inequality) and `s(f) ≤ deg(f)^2`, verified for every Boolean function of three
  variables. -/
theorem huang_sensitivity :
    (∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
        (sens f = 0 ↔ degree f = 0) ∧ (sens f ≤ 1 ↔ degree f ≤ 1)) ∧
      (∀ f : (Fin 3 → Bool) → Bool, degree f ≤ sens f ^ 2 ∧ sens f ≤ degree f ^ 2) := by
  constructor
  · intro n f
    refine ⟨?_, ⟨degree_le_one_of_sens_le_one, sens_le_one_of_degree_le_one⟩⟩
    rw [sens_eq_zero_iff_const, degree_eq_zero_iff_const]
  · intro f
    have hf : (fun x : Fin 3 → Bool => (fun a b c => f ![a, b, c]) (x 0) (x 1) (x 2)) = f := by
      funext x
      have hx : ![x 0, x 1, x 2] = x := by
        funext i
        fin_cases i <;> rfl
      show f ![x 0, x 1, x 2] = f x
      rw [hx]
    have h3 := huang_three_vars (fun a b c => f ![a, b, c])
    rwa [hf] at h3

end Frontier

