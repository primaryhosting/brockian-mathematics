import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/
lemma repr_unique {p q : Finset (Fin n) → ℝ}
    (h : ∀ x : Q n, ∑ T : Finset (Fin n), p T * mono T x
      = ∑ T : Finset (Fin n), q T * mono T x) : p = q := by
  funext T
  have hz : ∀ x : Q n, ∑ T : Finset (Fin n), (p T - q T) * mono T x = 0 := by
    intro x
    have := h x
    rw [Finset.sum_congr rfl (fun T _ => sub_mul (p T) (q T) (mono T x)),
      Finset.sum_sub_distrib, this, sub_self]
  have := mono_indep (fun T => p T - q T) hz T
  linarith [this]

/-- The coefficients of the multilinear representation of `f`. -/
noncomputable def coeff (f : Q n → Bool) : Finset (Fin n) → ℝ :=
  (exists_multilinear_repr (fun x => if f x then (1 : ℝ) else 0)).choose

lemma coeff_spec (f : Q n → Bool) :
    ∀ x : Q n, (if f x then (1 : ℝ) else 0) = ∑ T : Finset (Fin n), coeff f T * mono T x :=
  (exists_multilinear_repr (fun x => if f x then (1 : ℝ) else 0)).choose_spec

lemma eq_coeff_of_repr {f : Q n → Bool} {p : Finset (Fin n) → ℝ}
    (hp : ∀ x : Q n, (if f x then (1 : ℝ) else 0) = ∑ T : Finset (Fin n), p T * mono T x) :
    p = coeff f :=
  repr_unique (fun x => by rw [← hp x, coeff_spec f x])

/-- The degree of a Boolean function: the least `d` with a representing multilinear
polynomial of degree at most `d`. -/
noncomputable def bdeg (f : Q n → Bool) : ℕ := sInf {d | HasDegLE f d}

lemma hasDegLE_top (f : Q n → Bool) : HasDegLE f n := by
  refine ⟨coeff f, ?_, coeff_spec f⟩
  intro T hT
  have := Finset.card_le_univ T
  rw [Fintype.card_fin] at this
  omega

lemma hasDegLE_bdeg (f : Q n → Bool) : HasDegLE f (bdeg f) := by
  have h : bdeg f ∈ {d | HasDegLE f d} := Nat.sInf_mem ⟨n, hasDegLE_top f⟩
  exact h

lemma bdeg_le {f : Q n → Bool} {d : ℕ} (h : HasDegLE f d) : bdeg f ≤ d := Nat.sInf_le h

lemma hasDegLE_mono {f : Q n → Bool} {a b : ℕ} (h : HasDegLE f a) (hab : a ≤ b) :
    HasDegLE f b := by
  obtain ⟨p, hp0, hp⟩ := h
  exact ⟨p, fun T hT => hp0 T (lt_of_le_of_lt hab hT), hp⟩

lemma coeff_eq_zero_of_lt {f : Q n → Bool} {T : Finset (Fin n)} (hT : bdeg f < T.card) :
    coeff f T = 0 := by
  obtain ⟨p, hp0, hp⟩ := hasDegLE_bdeg f
  rw [← eq_coeff_of_repr hp]
  exact hp0 T hT

/-- Some coefficient of maximal degree is nonzero. -/
lemma exists_coeff_ne_zero (f : Q n → Bool) (hd : 0 < bdeg f) :
    ∃ T : Finset (Fin n), T.card = bdeg f ∧ coeff f T ≠ 0 := by
  by_contra hc
  push_neg at hc
  have : HasDegLE f (bdeg f - 1) := by
    refine ⟨coeff f, ?_, coeff_spec f⟩
    intro T hT
    rcases lt_trichotomy T.card (bdeg f) with h | h | h
    · omega
    · exact hc T h
    · exact coeff_eq_zero_of_lt h
  have := bdeg_le this
  omega

end Coeff

section Restriction

variable {n d : ℕ}

/-- The `j`-th element of `T`, as a coordinate of the big cube. -/
def emb (T : Finset (Fin n)) (hd : T.card = d) (j : Fin d) : Fin n :=
  (T.orderIsoOfFin hd j : Fin n)

/-- The extension of a vertex of the `d`-cube to a vertex of the `n`-cube, supported on `T`. -/
def ext (T : Finset (Fin n)) (hd : T.card = d) (y : Q d) : Q n :=
  fun i => if h : i ∈ T then y ((T.orderIsoOfFin hd).symm ⟨i, h⟩) else false

variable (T : Finset (Fin n)) (hd : T.card = d)

lemma emb_mem (j : Fin d) : emb T hd j ∈ T := (T.orderIsoOfFin hd j).2

lemma emb_injective : Function.Injective (emb T hd) := by
  intro i j h
  have : (T.orderIsoOfFin hd) i = (T.orderIsoOfFin hd) j := Subtype.ext h
  exact (T.orderIsoOfFin hd).injective this

lemma ext_emb (y : Q d) (j : Fin d) : ext T hd y (emb T hd j) = y j := by
  unfold ext
  rw [dif_pos (emb_mem T hd j)]
  congr 1
  have : (⟨emb T hd j, emb_mem T hd j⟩ : {x // x ∈ T}) = (T.orderIsoOfFin hd) j := rfl
  rw [this, OrderIso.symm_apply_apply]

lemma ext_of_not_mem (y : Q d) {i : Fin n} (hi : i ∉ T) : ext T hd y i = false := by
  simp [ext, hi]

lemma exists_emb_eq {i : Fin n} (hi : i ∈ T) : ∃ j : Fin d, emb T hd j = i := by
  refine ⟨(T.orderIsoOfFin hd).symm ⟨i, hi⟩, ?_⟩
  have : (T.orderIsoOfFin hd) ((T.orderIsoOfFin hd).symm ⟨i, hi⟩) = ⟨i, hi⟩ :=
    OrderIso.apply_symm_apply _ _
  exact congrArg Subtype.val this

lemma image_emb_univ : (univ : Finset (Fin d)).image (emb T hd) = T := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hi
    exact emb_mem T hd j
  · intro hi
    obtain ⟨j, rfl⟩ := exists_emb_eq T hd hi
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩

lemma ext_flipAt (y : Q d) (j : Fin d) :
    ext T hd (flipAt y j) = flipAt (ext T hd y) (emb T hd j) := by
  funext i
  by_cases hi : i ∈ T
  · obtain ⟨k, rfl⟩ := exists_emb_eq T hd hi
    rcases eq_or_ne k j with rfl | hkj
    · rw [ext_emb, flipAt_apply_self, flipAt_apply_self, ext_emb]
    · have hne : emb T hd k ≠ emb T hd j := fun h => hkj (emb_injective T hd h)
      rw [ext_emb, flipAt_apply_of_ne _ hkj, flipAt_apply_of_ne _ hne, ext_emb]
  · have hne : i ≠ emb T hd j := fun h => hi (h ▸ emb_mem T hd j)
    rw [ext_of_not_mem T hd _ hi, flipAt_apply_of_ne _ hne, ext_of_not_mem T hd _ hi]

lemma preimage_image_emb {T' : Finset (Fin n)} (hT' : T' ⊆ T) :
    (univ.filter (fun j : Fin d => emb T hd j ∈ T')).image (emb T hd) = T' := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    exact (Finset.mem_filter.1 hj).2
  · intro hi
    obtain ⟨j, rfl⟩ := exists_emb_eq T hd (hT' hi)
    exact Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ j, hi⟩, rfl⟩

lemma mono_ext_of_subset {T' : Finset (Fin n)} (hT' : T' ⊆ T) (y : Q d) :
    mono T' (ext T hd y) = mono (univ.filter (fun j : Fin d => emb T hd j ∈ T')) y := by
  have hTU : T' = (univ.filter (fun j : Fin d => emb T hd j ∈ T')).image (emb T hd) :=
    (preimage_image_emb T hd hT').symm
  calc mono T' (ext T hd y)
      = ∏ i ∈ (univ.filter (fun j : Fin d => emb T hd j ∈ T')).image (emb T hd),
          (if ext T hd y i then (1 : ℝ) else 0) := by rw [mono, ← hTU]
    _ = ∏ j ∈ univ.filter (fun j : Fin d => emb T hd j ∈ T'),
          (if ext T hd y (emb T hd j) then (1 : ℝ) else 0) :=
        Finset.prod_image (fun a _ b _ h => emb_injective T hd h)
    _ = mono (univ.filter (fun j : Fin d => emb T hd j ∈ T')) y := by
        exact Finset.prod_congr rfl (fun j _ => by rw [ext_emb])

lemma mono_ext_of_not_subset {T' : Finset (Fin n)} (hT' : ¬ T' ⊆ T) (y : Q d) :
    mono T' (ext T hd y) = 0 := by
  obtain ⟨i, hiT', hiT⟩ := Finset.not_subset.1 hT'
  exact Finset.prod_eq_zero hiT' (by rw [ext_of_not_mem T hd _ hiT]; simp)

/-- The restriction of `f` to the subcube spanned by the coordinates in `T`. -/
def restrict (f : Q n → Bool) : Q d → Bool := fun y => f (ext T hd y)

lemma sens_restrict_le (f : Q n → Bool) (y : Q d) :
    sens (restrict T hd f) y ≤ sens f (ext T hd y) := by
  refine Finset.card_le_card_of_injOn (emb T hd) (fun j hj => ?_)
    (fun a _ b _ h => emb_injective T hd h)
  rw [Finset.mem_coe, Finset.mem_filter] at hj
  rw [Finset.mem_coe, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have h := hj.2
  unfold restrict at h
  rw [ext_flipAt] at h
  exact h

lemma sensitivity_restrict_le (f : Q n → Bool) :
    sensitivity (restrict T hd f) ≤ sensitivity f := by
  unfold sensitivity
  refine Finset.sup_le (fun y _ => ?_)
  exact (sens_restrict_le T hd f y).trans
    (Finset.le_sup (f := sens f) (Finset.mem_univ (ext T hd y)))

/-- The alternating sum of the restriction picks out the top coefficient. -/
lemma topSum_restrict (f : Q n → Bool) :
    topSum (restrict T hd f) = coeff f T * sgn (fun _ : Fin d => true) := by
  have hstep : ∀ y : Q d, sgn y * (if restrict T hd f y then (1 : ℝ) else 0)
      = ∑ T' : Finset (Fin n), coeff f T' * (sgn y * mono T' (ext T hd y)) := by
    intro y
    unfold restrict
    rw [coeff_spec f (ext T hd y), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun T' _ => by ring)
  unfold topSum
  rw [Finset.sum_congr rfl (fun y _ => hstep y), Finset.sum_comm]
  rw [Finset.sum_eq_single T]
  · rw [← Finset.mul_sum]
    congr 1
    have hUT : (univ.filter (fun j : Fin d => emb T hd j ∈ T)) = univ := by
      ext j
      simp [emb_mem T hd j]
    have : ∀ y : Q d, sgn y * mono T (ext T hd y) = sgn y * mono (univ : Finset (Fin d)) y := by
      intro y
      rw [mono_ext_of_subset T hd (subset_refl T) y, hUT]
    rw [Finset.sum_congr rfl (fun y _ => this y), sum_sgn_mono_univ]
  · intro T' _ hT'
    by_cases hsub : T' ⊆ T
    · have hU : (univ.filter (fun j : Fin d => emb T hd j ∈ T')) ≠ univ := by
        intro hU
        refine hT' (le_antisymm hsub ?_)
        intro i hi
        obtain ⟨j, rfl⟩ := exists_emb_eq T hd hi
        have : j ∈ univ.filter (fun j : Fin d => emb T hd j ∈ T') := by rw [hU]; exact mem_univ j
        exact (Finset.mem_filter.1 this).2
      have : ∀ y : Q d, sgn y * mono T' (ext T hd y)
          = sgn y * mono (univ.filter (fun j : Fin d => emb T hd j ∈ T')) y :=
        fun y => by rw [mono_ext_of_subset T hd hsub y]
      rw [← Finset.mul_sum, Finset.sum_congr rfl (fun y _ => this y),
        sum_sgn_mono _ hU, mul_zero]
    · have : ∀ y : Q d, sgn y * mono T' (ext T hd y) = 0 :=
        fun y => by rw [mono_ext_of_not_subset T hd hsub y, mul_zero]
      rw [← Finset.mul_sum, Finset.sum_congr rfl (fun y _ => this y), Finset.sum_const_zero,
        mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

end Restriction

section Main

variable {n : ℕ}

/-- **Huang's sensitivity theorem**: the sensitivity of a Boolean function is at least the
square root of its degree. -/
theorem huang_sensitivity_sqrt_deg (f : Q n → Bool) :
    Real.sqrt (bdeg f) ≤ sensitivity f := by
  rcases Nat.eq_zero_or_pos (bdeg f) with h0 | hpos
  · rw [h0]
    simp
  obtain ⟨T, hTcard, hTne⟩ := exists_coeff_ne_zero f hpos
  set d := bdeg f with hdeq
  have hd : T.card = d := hTcard
  set g : Q d → Bool := restrict T hd f with hg
  have hts : topSum g ≠ 0 := by
    rw [hg, topSum_restrict T hd f]
    rcases mul_self_eq_one_iff.1 (sgn_mul_self (fun _ : Fin d => true)) with h1 | h1 <;>
      rw [h1] <;> simpa using hTne
  have hdeg : ¬ HasDegLE g (d - 1) := fun hc => hts (topSum_eq_zero_of_hasDegLE hpos hc)
  have hmain : Real.sqrt d ≤ sensitivity g := huang_sensitivity hpos g hdeg
  refine hmain.trans ?_
  exact_mod_cast sensitivity_restrict_le T hd f

/-- A sanity check: the two-variable `AND` function has degree `2`. -/
theorem bdeg_and_two : bdeg (fun x : Q 2 => x 0 && x 1) = 2 := by
  have hle : bdeg (fun x : Q 2 => x 0 && x 1) ≤ 2 := bdeg_le (hasDegLE_top _)
  have hnot : ¬ HasDegLE (fun x : Q 2 => x 0 && x 1) 1 := by
    intro hdeg
    have h := topSum_eq_zero_of_hasDegLE (n := 2) (by norm_num) hdeg
    rw [topSum_eq (by norm_num)] at h
    have hcard : (univ.filter (fun x : Q 2 => (x 0 && x 1) ≠ par x)).card = 3 := by decide
    rw [hcard] at h
    norm_num at h
  have hgt : ¬ (bdeg (fun x : Q 2 => x 0 && x 1) ≤ 1) :=
    fun hb => hnot (hasDegLE_mono (hasDegLE_bdeg _) hb)
  omega

end Main

end Frontier

import RequestProject.Huang

open Finset

namespace Frontier

/-! # Degree of a Boolean function and Huang's theorem in the full-degree case

Every Boolean function `f : {0,1}^n → {0,1}` is represented by a unique multilinear
polynomial with real coefficients.  We define `Frontier.HasDegLE f d` to mean that `f` is
represented by a multilinear polynomial all of whose monomials have degree at most `d`, so
that "`f` has degree `n`" is `¬ HasDegLE f (n-1)`.

The main result `Frontier.huang_sensitivity` states that a Boolean function of full degree
`n` has sensitivity at least `√n`.
-/

section Multilinear

variable {n : ℕ}

/-- The multilinear monomial `∏ i ∈ T, x i`, evaluated at a hypercube vertex. -/
def mono (T : Finset (Fin n)) (x : Q n) : ℝ := ∏ i ∈ T, (if x i then (1 : ℝ) else 0)

/-- The vertex which is the indicator function of `T`. -/
def indic (T : Finset (Fin n)) : Q n := fun i => decide (i ∈ T)

lemma mono_indic (T T' : Finset (Fin n)) : mono T (indic T') = if T ⊆ T' then 1 else 0 := by
  unfold mono indic
  by_cases h : T ⊆ T'
  · rw [if_pos h]
    refine Finset.prod_eq_one (fun i hi => ?_)
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hiT, hiT'⟩ := Finset.not_subset.1 h
    refine Finset.prod_eq_zero hiT ?_
    simp [hiT']

lemma mono_univ (x : Q n) : mono univ x = if x = (fun _ => true) then 1 else 0 := by
  unfold mono
  by_cases h : x = (fun _ => true)
  · rw [if_pos h]
    refine Finset.prod_eq_one (fun i _ => ?_)
    simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i = false := by
      by_contra hc
      push_neg at hc
      exact h (funext (fun i => by simpa using hc i))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The multilinear monomials are linearly independent. -/
lemma mono_indep (c : Finset (Fin n) → ℝ)
    (h : ∀ x : Q n, ∑ T : Finset (Fin n), c T * mono T x = 0) : ∀ T, c T = 0 := by
  intro T
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    have h0 := h (indic T)
    have hsum : ∑ T' : Finset (Fin n), c T' * mono T' (indic T) = ∑ T' ∈ T.powerset, c T' := by
      simp only [mono_indic, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext T'
      simp [Finset.mem_powerset]
    rw [hsum] at h0
    have hmemT : T ∈ T.powerset := Finset.mem_powerset_self T
    rw [← Finset.add_sum_erase _ _ hmemT] at h0
    have hzero : ∑ T' ∈ (T.powerset).erase T, c T' = 0 := by
      refine Finset.sum_eq_zero (fun T' hT' => ?_)
      have hne : T' ≠ T := (Finset.mem_erase.1 hT').1
      have hsub : T' ⊆ T := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hT')
      exact ih T' (lt_of_le_of_ne hsub hne)
    rw [hzero, add_zero] at h0
    exact h0

/-- Every real-valued function on the hypercube is a multilinear polynomial. -/
lemma exists_multilinear_repr (g : Q n → ℝ) :
    ∃ p : Finset (Fin n) → ℝ, ∀ x, g x = ∑ T : Finset (Fin n), p T * mono T x := by
  classical
  have hli : LinearIndependent ℝ (fun T : Finset (Fin n) => (mono T : Q n → ℝ)) := by
    refine Fintype.linearIndependent_iff.2 (fun c hc T => ?_)
    refine mono_indep c (fun x => ?_) T
    have := congrFun hc x
    simpa using this
  have hcard : Fintype.card (Finset (Fin n)) = Module.finrank ℝ (Q n → ℝ) := by
    simp [Module.finrank_fintype_fun_eq_card]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = fun T : Finset (Fin n) => (mono T : Q n → ℝ) :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨fun T => b.repr g T, fun x => ?_⟩
  have := b.sum_repr g
  rw [hb] at this
  have := congrFun this x
  simpa [Finset.sum_apply] using this.symm

end Multilinear

section Degree

variable {n : ℕ}

/-- `HasDegLE f d` means that the Boolean function `f` is represented by a multilinear
polynomial with real coefficients all of whose monomials have degree at most `d`. -/
def HasDegLE (f : Q n → Bool) (d : ℕ) : Prop :=
  ∃ p : Finset (Fin n) → ℝ, (∀ T : Finset (Fin n), d < T.card → p T = 0) ∧
    ∀ x : Q n, (if f x then (1 : ℝ) else 0) = ∑ T : Finset (Fin n), p T * mono T x

/-- The alternating sum `∑ₓ (-1)^{|x|} f(x)`; it is, up to sign, the coefficient of
`x₁ ⋯ xₙ` in the multilinear representation of `f`. -/
def topSum (f : Q n → Bool) : ℝ := ∑ x : Q n, sgn x * (if f x then (1 : ℝ) else 0)

lemma sgn_eq_of_par (x : Q n) : sgn x = if par x then -1 else 1 := by
  by_cases h : par x = true
  · rw [if_pos h]
    exact (par_eq_true_iff x).1 h
  · rw [if_neg (by simpa using h)]
    rcases mul_self_eq_one_iff.1 (sgn_mul_self x) with h1 | h1
    · exact h1
    · exact absurd ((par_eq_true_iff x).2 h1) (by simpa using h)

/-- The alternating sum of a monomial of degree `< n` vanishes. -/
lemma sum_sgn_mono (T : Finset (Fin n)) (hT : T ≠ univ) :
    ∑ x : Q n, sgn x * mono T x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
    by_contra hc
    push_neg at hc
    exact hT (Finset.eq_univ_iff_forall.2 hc)
  refine Finset.sum_ninvolution (fun x => flipAt x i) ?_ ?_ (fun _ => Finset.mem_univ _) ?_
  · intro x
    have hmono : mono T (flipAt x i) = mono T x := by
      unfold mono
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [flipAt_apply_of_ne _ hji]
    rw [hmono, sgn_flipAt]
    ring
  · intro x _
    exact flipAt_ne_self x i
  · intro x
    exact flipAt_flipAt x i

lemma sum_sgn_mono_univ : ∑ x : Q n, sgn x * mono univ x = sgn (fun _ : Fin n => true) := by
  rw [Finset.sum_congr rfl (fun x _ => by rw [mono_univ])]
  rw [Finset.sum_eq_single (fun _ => true : Q n)]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The number of odd-weight vertices of the `n`-cube is `2^(n-1)`. -/
lemma card_par (hn : 1 ≤ n) :
    (univ.filter (fun x : Q n => par x = true)).card = 2 ^ (n - 1) := by
  have hne : (∅ : Finset (Fin n)) ≠ univ := by
    intro h
    have : (⟨0, hn⟩ : Fin n) ∈ (∅ : Finset (Fin n)) := by rw [h]; exact Finset.mem_univ _
    simp at this
  have h0 : ∑ x : Q n, sgn x = 0 := by
    have := sum_sgn_mono (∅ : Finset (Fin n)) hne
    simpa [mono] using this
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Q n))
    (fun x : Q n => par x = true) sgn
  have hA : ∑ x ∈ univ.filter (fun x : Q n => par x = true), sgn x
      = -((univ.filter (fun x : Q n => par x = true)).card : ℝ) := by
    have hval : ∀ x ∈ univ.filter (fun x : Q n => par x = true), sgn x = -1 := by
      intro x hx
      rw [sgn_eq_of_par, if_pos (Finset.mem_filter.1 hx).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    ring
  have hB : ∑ x ∈ univ.filter (fun x : Q n => ¬ (par x = true)), sgn x
      = ((univ.filter (fun x : Q n => ¬ (par x = true))).card : ℝ) := by
    have hval : ∀ x ∈ univ.filter (fun x : Q n => ¬ (par x = true)), sgn x = 1 := by
      intro x hx
      rw [sgn_eq_of_par, if_neg (Finset.mem_filter.1 hx).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hA, hB, h0] at hsplit
  have hcards : (univ.filter (fun x : Q n => par x = true)).card
      + (univ.filter (fun x : Q n => ¬ (par x = true))).card = 2 ^ n := by
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Q n))) (p := fun x : Q n => par x = true)
    simpa using this
  have heq : (univ.filter (fun x : Q n => par x = true)).card
      = (univ.filter (fun x : Q n => ¬ (par x = true))).card := by
    have : ((univ.filter (fun x : Q n => par x = true)).card : ℝ)
        = ((univ.filter (fun x : Q n => ¬ (par x = true))).card : ℝ) := by linarith
    exact_mod_cast this
  have hpow : (2 : ℕ) ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  omega

/-- The alternating sum computes the size of the set where `f` differs from parity. -/
lemma topSum_eq (hn : 1 ≤ n) (f : Q n → Bool) :
    topSum f = ((univ.filter (fun x => f x ≠ par x)).card : ℝ) - 2 ^ (n - 1) := by
  have hpt : ∀ x : Q n, sgn x * (if f x then (1 : ℝ) else 0)
      = (if f x ≠ par x then (1 : ℝ) else 0) - (if par x then (1 : ℝ) else 0) := by
    intro x
    rw [sgn_eq_of_par]
    by_cases hp : par x = true <;> by_cases hf : f x = true <;>
      simp [hp, hf]
  unfold topSum
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.sum_boole, card_par hn]
  norm_num

lemma topSum_eq_zero_of_hasDegLE (hn : 1 ≤ n) {f : Q n → Bool} (h : HasDegLE f (n - 1)) :
    topSum f = 0 := by
  obtain ⟨p, hp, hrep⟩ := h
  have hstep : ∀ x : Q n, sgn x * (if f x then (1 : ℝ) else 0)
      = ∑ T : Finset (Fin n), p T * (sgn x * mono T x) := by
    intro x
    rw [hrep x, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun T _ => by ring)
  unfold topSum
  rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_comm]
  refine Finset.sum_eq_zero (fun T _ => ?_)
  by_cases hT : T = univ
  · have hpT : p T = 0 := by
      refine hp T ?_
      rw [hT, Finset.card_univ, Fintype.card_fin]
      omega
    simp [hpT]
  · rw [← Finset.mul_sum, sum_sgn_mono T hT, mul_zero]

lemma hasDegLE_of_topSum_eq_zero (hn : 1 ≤ n) (f : Q n → Bool) (h : topSum f = 0) :
    HasDegLE f (n - 1) := by
  obtain ⟨p, hp⟩ := exists_multilinear_repr (fun x => if f x then (1 : ℝ) else 0)
  have huniv : p univ = 0 := by
    have hstep : ∀ x : Q n, sgn x * (if f x then (1 : ℝ) else 0)
        = ∑ T : Finset (Fin n), p T * (sgn x * mono T x) := by
      intro x
      rw [hp x, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun T _ => by ring)
    have hts : topSum f = p univ * sgn (fun _ : Fin n => true) := by
      unfold topSum
      rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_comm]
      rw [Finset.sum_eq_single (univ : Finset (Fin n))]
      · rw [← Finset.mul_sum, sum_sgn_mono_univ]
      · intro T _ hT
        rw [← Finset.mul_sum, sum_sgn_mono T hT, mul_zero]
      · intro hc
        exact absurd (Finset.mem_univ _) hc
    rw [h] at hts
    rcases mul_self_eq_one_iff.1 (sgn_mul_self (fun _ => true : Q n)) with h1 | h1 <;>
      rw [h1] at hts <;> linarith
  refine ⟨p, ?_, hp⟩
  intro T hT
  have hTu : T = univ := by
    refine Finset.eq_univ_of_card T ?_
    have hle := Finset.card_le_univ T
    rw [Fintype.card_fin] at hle ⊢
    omega
  rw [hTu, huniv]

/-- **Huang's sensitivity theorem** in the full-degree case: a Boolean function on `n ≥ 1`
variables whose multilinear representation has degree `n` (i.e. which is not represented by
any multilinear polynomial of degree at most `n - 1`) has sensitivity at least `√n`. -/
theorem huang_sensitivity (hn : 1 ≤ n) (f : Q n → Bool) (hdeg : ¬ HasDegLE f (n - 1)) :
    Real.sqrt n ≤ sensitivity f := by
  refine huang_sensitivity_of_card_ne hn f ?_
  intro hcard
  refine hdeg (hasDegLE_of_topSum_eq_zero hn f ?_)
  rw [topSum_eq hn f, hcard]
  push_cast
  ring

/-- A sanity check that the hypothesis of `Frontier.huang_sensitivity` is satisfiable: the
two-variable `AND` function has full degree `2`, hence sensitivity at least `√2`. -/
theorem sensitivity_and_two : Real.sqrt 2 ≤ sensitivity (fun x : Q 2 => x 0 && x 1) := by
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [← h2]
  refine huang_sensitivity (by norm_num) _ ?_
  intro hdeg
  have h := topSum_eq_zero_of_hasDegLE (n := 2) (by norm_num) hdeg
  rw [topSum_eq (by norm_num)] at h
  have hcard : (univ.filter (fun x : Q 2 => (x 0 && x 1) ≠ par x)).card = 3 := by decide
  rw [hcard] at h
  norm_num at h

end Degree

end Frontier

import Mathlib
import RequestProject.Huang
import RequestProject.Degree
import RequestProject.Full

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

import Mathlib

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem (the `deg = n` case)

We formalise Huang's 2019 theorem.  The combinatorial core is:

* `Frontier.huang_cube` : every set `S` of more than `2^(n-1)` vertices of the Boolean
  hypercube `{0,1}^n` contains a vertex with at least `√n` neighbours inside `S`.

From it we deduce the sensitivity statement `Frontier.huang_sensitivity`.
-/

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Flip the `i`-th coordinate of a hypercube vertex. -/
def flipAt {n : ℕ} (x : Q n) (i : Fin n) : Q n := Function.update x i (!x i)

section Flip

variable {n : ℕ}

@[simp] lemma flipAt_apply_self (x : Q n) (i : Fin n) : flipAt x i i = !x i := by
  simp [flipAt]

lemma flipAt_apply_of_ne (x : Q n) {i j : Fin n} (h : j ≠ i) : flipAt x i j = x j := by
  simp [flipAt, h]

@[simp] lemma flipAt_flipAt (x : Q n) (i : Fin n) : flipAt (flipAt x i) i = x := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [flipAt_apply_of_ne _ h]

lemma flipAt_ne_self (x : Q n) (i : Fin n) : flipAt x i ≠ x := by
  intro h
  have := congrFun h i
  simp at this

lemma flipAt_comm (x : Q n) (i j : Fin n) :
    flipAt (flipAt x i) j = flipAt (flipAt x j) i := by
  funext k
  rcases eq_or_ne k i with rfl | hki
  · rcases eq_or_ne k j with rfl | hkj
    · rfl
    · simp [flipAt_apply_of_ne _ hkj]
  · rcases eq_or_ne k j with rfl | hkj
    · simp [flipAt_apply_of_ne _ hki]
    · simp [flipAt_apply_of_ne _ hki, flipAt_apply_of_ne _ hkj]

lemma flipAt_inj (x : Q n) {i j : Fin n} (h : flipAt x i = flipAt x j) : i = j := by
  by_contra hij
  have := congrFun h i
  rw [flipAt_apply_self, flipAt_apply_of_ne _ hij] at this
  simp at this

end Flip

section Sign

variable {n : ℕ}

/-- Number of coordinates `k` satisfying `p k` at which `x` is `true`. -/
def cnt (p : Fin n → Prop) [DecidablePred p] (x : Q n) : ℕ :=
  (univ.filter (fun k => p k ∧ x k = true)).card

/-- The `±1` sign attached to a set of coordinates. -/
def sgnp (p : Fin n → Prop) [DecidablePred p] (x : Q n) : ℝ := (-1) ^ cnt p x

lemma sgnp_mul_self (p : Fin n → Prop) [DecidablePred p] (x : Q n) :
    sgnp p x * sgnp p x = 1 := by
  simp [sgnp, ← pow_add, ← two_mul, pow_mul]

lemma sgnp_flip_of_not (p : Fin n → Prop) [DecidablePred p] (x : Q n) {j : Fin n}
    (hj : ¬ p j) : sgnp p (flipAt x j) = sgnp p x := by
  have : cnt p (flipAt x j) = cnt p x := by
    unfold cnt
    congr 1
    apply Finset.filter_congr
    intro k _
    rcases eq_or_ne k j with rfl | hk
    · simp [hj]
    · simp [flipAt_apply_of_ne _ hk]
  simp [sgnp, this]

lemma sgnp_flip_of_mem (p : Fin n → Prop) [DecidablePred p] (x : Q n) {j : Fin n}
    (hj : p j) : sgnp p (flipAt x j) = - sgnp p x := by
  by_cases hx : x j = true
  · have hmem : j ∈ univ.filter (fun k => p k ∧ x k = true) := by simp [hj, hx]
    have hset : univ.filter (fun k => p k ∧ (flipAt x j) k = true)
        = (univ.filter (fun k => p k ∧ x k = true)).erase j := by
      ext k
      by_cases hk : k = j
      · subst hk; simp [hx]
      · simp [flipAt_apply_of_ne _ hk, hk]
    have hcard : cnt p (flipAt x j) + 1 = cnt p x := by
      unfold cnt
      rw [hset, Finset.card_erase_of_mem hmem]
      exact Nat.succ_pred_eq_of_pos (Finset.card_pos.2 ⟨j, hmem⟩)
    unfold sgnp
    rw [← hcard]
    ring
  · have hx' : x j = false := by simpa using hx
    have hnot : j ∉ univ.filter (fun k => p k ∧ x k = true) := by simp [hx']
    have hset : univ.filter (fun k => p k ∧ (flipAt x j) k = true)
        = insert j (univ.filter (fun k => p k ∧ x k = true)) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp [hx', hj]
      · simp [flipAt_apply_of_ne _ hk, hk]
    have hcard : cnt p (flipAt x j) = cnt p x + 1 := by
      unfold cnt; rw [hset, Finset.card_insert_of_notMem hnot]
    unfold sgnp
    rw [hcard]
    ring

end Sign

section Matrix

variable {n : ℕ}

/-- The Huang sign of the edge `{x, flipAt x i}`. -/
def eps (x : Q n) (i : Fin n) : ℝ := sgnp (fun k => i < k) x

/-- The global sign, `(-1)` to the Hamming weight. -/
def sgn (x : Q n) : ℝ := sgnp (fun _ => True) x

lemma eps_mul_self (x : Q n) (i : Fin n) : eps x i * eps x i = 1 := sgnp_mul_self _ _

lemma eps_flipAt_self (x : Q n) (i : Fin n) : eps (flipAt x i) i = eps x i :=
  sgnp_flip_of_not _ _ (lt_irrefl i)

lemma eps_anticomm (x : Q n) {i j : Fin n} (hij : i ≠ j) :
    eps x i * eps (flipAt x i) j = - (eps x j * eps (flipAt x j) i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · have h1 : eps (flipAt x i) j = eps x j := sgnp_flip_of_not _ _ (asymm h)
    have h2 : eps (flipAt x j) i = - eps x i := sgnp_flip_of_mem _ _ h
    rw [h1, h2]; ring
  · have h1 : eps (flipAt x i) j = - eps x j := sgnp_flip_of_mem _ _ h
    have h2 : eps (flipAt x j) i = eps x i := sgnp_flip_of_not _ _ (asymm h)
    rw [h1, h2]; ring

lemma sgn_flipAt (x : Q n) (i : Fin n) : sgn (flipAt x i) = - sgn x :=
  sgnp_flip_of_mem _ _ trivial

lemma sgn_mul_self (x : Q n) : sgn x * sgn x = 1 := sgnp_mul_self _ _

/-- Huang's signed adjacency operator on the hypercube. -/
def hL (n : ℕ) : (Q n → ℝ) →ₗ[ℝ] (Q n → ℝ) where
  toFun v := fun x => ∑ i : Fin n, eps x i * v (flipAt x i)
  map_add' u v := by
    funext x
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c v := by
    funext x
    simp [Finset.mul_sum, mul_left_comm]

@[simp] lemma hL_apply (v : Q n → ℝ) (x : Q n) :
    hL n v x = ∑ i : Fin n, eps x i * v (flipAt x i) := rfl

/-- The key algebraic identity: the signed adjacency operator squares to `n`. -/
lemma hL_hL (v : Q n → ℝ) : hL n (hL n v) = (n : ℝ) • v := by
  funext x
  set F : Fin n → Fin n → ℝ :=
    fun i j => eps x i * (eps (flipAt x i) j * v (flipAt (flipAt x i) j)) with hFdef
  set H : Fin n → Fin n → ℝ := fun i j => if j = i then 0 else F i j with hHdef
  have hFdiag : ∀ i, F i i = v x := by
    intro i
    have : eps (flipAt x i) i = eps x i := eps_flipAt_self x i
    rw [hFdef]
    simp only [this, flipAt_flipAt]
    rw [← mul_assoc, eps_mul_self, one_mul]
  have hHanti : ∀ i j, H j i = - H i j := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · simp [hHdef]
    · have h1 : H i j = F i j := by simp [hHdef, Ne.symm hij]
      have h2 : H j i = F j i := by simp [hHdef, hij]
      rw [h1, h2, hFdef]
      simp only
      rw [flipAt_comm x j i, ← mul_assoc, ← mul_assoc, eps_anticomm x hij]
      ring
  have hHzero : ∑ i : Fin n, ∑ j : Fin n, H i j = 0 := by
    have h1 : ∑ i : Fin n, ∑ j : Fin n, H i j = ∑ i : Fin n, ∑ j : Fin n, H j i :=
      Finset.sum_comm
    have h2 : ∑ i : Fin n, ∑ j : Fin n, H j i = - ∑ i : Fin n, ∑ j : Fin n, H i j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => hHanti i j)
    have := h1.trans h2
    linarith
  have hsplit : ∀ i : Fin n, ∑ j : Fin n, F i j = F i i + ∑ j : Fin n, H i j := by
    intro i
    have : ∑ j : Fin n, H i j = (∑ j : Fin n, F i j) - F i i := by
      have : ∀ j : Fin n, H i j = F i j - (if j = i then F i j else 0) := by
        intro j; by_cases h : j = i <;> simp [hHdef, h]
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' univ i (fun j => F i j)]
      simp
    rw [this]; ring
  have hgoal : hL n (hL n v) x = ∑ i : Fin n, ∑ j : Fin n, F i j := by
    simp only [hL_apply, Finset.mul_sum, hFdef]
  rw [hgoal, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun i _ => hFdiag i), hHzero]
  simp [mul_comm]

/-- Conjugation by the global sign flips the sign of the operator. -/
lemma hL_sgn (v : Q n → ℝ) (x : Q n) :
    hL n (fun y => sgn y * v y) x = - (sgn x * hL n v x) := by
  simp only [hL_apply, sgn_flipAt, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

end Matrix

section Huang

variable {n : ℕ}

/-- Multiplication by the global sign `sgn`. -/
def Dlin (n : ℕ) : (Q n → ℝ) →ₗ[ℝ] (Q n → ℝ) where
  toFun v := fun x => sgn x * v x
  map_add' u v := by funext x; simp [mul_add]
  map_smul' c v := by funext x; simp [mul_left_comm]

@[simp] lemma Dlin_apply (v : Q n → ℝ) (x : Q n) : Dlin n v x = sgn x * v x := rfl

lemma Dlin_Dlin (v : Q n → ℝ) : Dlin n (Dlin n v) = v := by
  funext x
  simp [← mul_assoc, sgn_mul_self]

lemma Dlin_surjective : Function.Surjective (Dlin n) := fun v => ⟨Dlin n v, Dlin_Dlin v⟩

lemma Dlin_injective : Function.Injective (Dlin n) := by
  intro u v h
  have := congrArg (Dlin n) h
  rwa [Dlin_Dlin, Dlin_Dlin] at this

lemma hL_Dlin (v : Q n → ℝ) : hL n (Dlin n v) = - Dlin n (hL n v) := by
  funext x
  exact hL_sgn v x

/-- `hL + √n`. -/
noncomputable def Bop (n : ℕ) : (Q n → ℝ) →ₗ[ℝ] (Q n → ℝ) :=
  hL n + Real.sqrt n • LinearMap.id

/-- `√n - hL`. -/
noncomputable def Cop (n : ℕ) : (Q n → ℝ) →ₗ[ℝ] (Q n → ℝ) :=
  Real.sqrt n • LinearMap.id - hL n

lemma Bop_apply (v : Q n → ℝ) : Bop n v = hL n v + Real.sqrt n • v := rfl

lemma Cop_apply (v : Q n → ℝ) : Cop n v = Real.sqrt n • v - hL n v := rfl

lemma hL_Bop (v : Q n → ℝ) : hL n (Bop n v) = Real.sqrt n • Bop n v := by
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  rw [Bop_apply, map_add, map_smul, hL_hL, smul_add, smul_smul, hsq]
  abel

lemma Dlin_Cop_Dlin (v : Q n → ℝ) : Dlin n (Cop n (Dlin n v)) = Bop n v := by
  rw [Cop_apply, map_sub, map_smul, hL_Dlin, map_neg, Dlin_Dlin, Dlin_Dlin, Bop_apply]
  abel

lemma range_Bop_sup_range_Cop (hn : 1 ≤ n) :
    LinearMap.range (Bop n) ⊔ LinearMap.range (Cop n) = ⊤ := by
  have hpos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  refine eq_top_iff.2 (fun w _ => ?_)
  set u : Q n → ℝ := (2 * Real.sqrt n)⁻¹ • w with hu
  have hsum : Bop n u + Cop n u = (2 * Real.sqrt n) • u := by
    rw [Bop_apply, Cop_apply]
    module
  have hw : w = Bop n u + Cop n u := by
    rw [hsum, hu, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  rw [hw]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

lemma finrank_range_Cop_eq_finrank_range_Bop (n : ℕ) :
    Module.finrank ℝ (LinearMap.range (Cop n)) = Module.finrank ℝ (LinearMap.range (Bop n)) := by
  have hcomp : Bop n = (Dlin n) ∘ₗ ((Cop n) ∘ₗ (Dlin n)) :=
    LinearMap.ext (fun v => (Dlin_Cop_Dlin v).symm)
  have hrange : LinearMap.range (Bop n) = Submodule.map (Dlin n) (LinearMap.range (Cop n)) := by
    rw [hcomp, LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top (Cop n)
        (LinearMap.range_eq_top.2 (Dlin_surjective (n := n)))]
  rw [hrange]
  exact (Submodule.equivMapOfInjective (Dlin n) Dlin_injective _).finrank_eq

lemma finrank_range_Bop (hn : 1 ≤ n) :
    2 ^ (n - 1) ≤ Module.finrank ℝ (LinearMap.range (Bop n)) := by
  have hcard : Module.finrank ℝ (Q n → ℝ) = 2 ^ n := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hle : Module.finrank ℝ ((LinearMap.range (Bop n) ⊔ LinearMap.range (Cop n) :
      Submodule ℝ (Q n → ℝ)))
      ≤ Module.finrank ℝ (LinearMap.range (Bop n)) + Module.finrank ℝ (LinearMap.range (Cop n)) :=
    Submodule.finrank_add_le_finrank_add_finrank _ _
  rw [range_Bop_sup_range_Cop hn, finrank_range_Cop_eq_finrank_range_Bop] at hle
  rw [finrank_top, hcard] at hle
  have hpow : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  omega

/-- The subspace of vectors supported inside `S`. -/
noncomputable def suppSub (S : Finset (Q n)) : Submodule ℝ (Q n → ℝ) :=
  LinearMap.ker (LinearMap.funLeft ℝ ℝ (Subtype.val : {x : Q n // x ∉ S} → Q n))

lemma mem_suppSub {S : Finset (Q n)} {v : Q n → ℝ} :
    v ∈ suppSub S ↔ ∀ x, x ∉ S → v x = 0 := by
  constructor
  · intro hv x hx
    have := congrFun (LinearMap.mem_ker.1 hv) ⟨x, hx⟩
    simpa using this
  · intro hv
    refine LinearMap.mem_ker.2 ?_
    funext y
    simpa using hv y.1 y.2

lemma finrank_suppSub (S : Finset (Q n)) :
    Module.finrank ℝ (suppSub S) = S.card := by
  have hcard : Module.finrank ℝ (Q n → ℝ) = 2 ^ n := by
    simp [Module.finrank_fintype_fun_eq_card]
  set f : (Q n → ℝ) →ₗ[ℝ] ({x : Q n // x ∉ S} → ℝ) :=
    LinearMap.funLeft ℝ ℝ (Subtype.val : {x : Q n // x ∉ S} → Q n) with hf
  have hsurj : Function.Surjective f :=
    LinearMap.funLeft_surjective_of_injective ℝ ℝ _ Subtype.val_injective
  have h1 : Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker f)
      = Module.finrank ℝ (Q n → ℝ) := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hcard] at h1
  have h2 : Module.finrank ℝ ({x : Q n // x ∉ S} → ℝ) = 2 ^ n - S.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl]
    simp [Fintype.card_coe]
  have h3 : S.card ≤ 2 ^ n := by
    have := Finset.card_le_univ S
    simpa using this
  rw [h2, hf] at h1
  unfold suppSub
  generalize (2 : ℕ) ^ n = M at h1 h3
  omega

/-- The existence of an eigenvector of the signed adjacency operator supported in `S`. -/
lemma exists_eigenvector (hn : 1 ≤ n) (S : Finset (Q n)) (hS : 2 ^ (n - 1) < S.card) :
    ∃ v : Q n → ℝ, v ≠ 0 ∧ (∀ x, x ∉ S → v x = 0) ∧ hL n v = Real.sqrt n • v := by
  have hcard : Module.finrank ℝ (Q n → ℝ) = 2 ^ n := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hpow : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  set W : Submodule ℝ (Q n → ℝ) := suppSub S with hW
  set V : Submodule ℝ (Q n → ℝ) := LinearMap.range (Bop n) with hV
  have hWrank : Module.finrank ℝ W = S.card := finrank_suppSub S
  have hVrank : 2 ^ (n - 1) ≤ Module.finrank ℝ V := finrank_range_Bop hn
  have hsup : Module.finrank ℝ ((W ⊔ V : Submodule ℝ (Q n → ℝ))) ≤ 2 ^ n := by
    rw [← hcard]; exact Submodule.finrank_le _
  have hinf : Module.finrank ℝ ((W ⊔ V : Submodule ℝ (Q n → ℝ)))
      + Module.finrank ℝ ((W ⊓ V : Submodule ℝ (Q n → ℝ)))
      = Module.finrank ℝ W + Module.finrank ℝ V :=
    Submodule.finrank_sup_add_finrank_inf_eq W V
  have hpos : 0 < Module.finrank ℝ ((W ⊓ V : Submodule ℝ (Q n → ℝ))) := by omega
  have hne : (W ⊓ V : Submodule ℝ (Q n → ℝ)) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨v, hvmem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, ?_, ?_⟩
  · exact mem_suppSub.1 (Submodule.mem_inf.1 hvmem).1
  · obtain ⟨w, hw⟩ := (Submodule.mem_inf.1 hvmem).2
    rw [← hw]
    exact hL_Bop w

/-- Huang's theorem: any set of more than half of the vertices of the `n`-cube contains a
vertex with at least `√n` neighbours in the set. -/
theorem huang_cube (hn : 1 ≤ n) (S : Finset (Q n)) (hS : 2 ^ (n - 1) < S.card) :
    ∃ x ∈ S, Real.sqrt n ≤ (univ.filter (fun i : Fin n => flipAt x i ∈ S)).card := by
  obtain ⟨v, hv0, hsupp, heig⟩ := exists_eigenvector hn S hS
  obtain ⟨x, hx⟩ : ∃ x : Q n, ∀ y : Q n, |v y| ≤ |v x| := Finite.exists_max _
  have hvx : 0 < |v x| := by
    obtain ⟨y, hy⟩ : ∃ y, v y ≠ 0 := by
      by_contra hc
      exact hv0 (funext (fun y => by simpa using not_exists.1 hc y))
    exact lt_of_lt_of_le (abs_pos.2 hy) (hx y)
  have hxS : x ∈ S := by
    by_contra hc
    rw [hsupp x hc] at hvx
    simp at hvx
  refine ⟨x, hxS, ?_⟩
  set F : Finset (Fin n) := univ.filter (fun i : Fin n => flipAt x i ∈ S) with hF
  have habs : ∀ i : Fin n, |eps x i| = 1 := by
    intro i
    rw [eps, sgnp, abs_pow, abs_neg, abs_one, one_pow]
  have key : Real.sqrt n * |v x| ≤ (F.card : ℝ) * |v x| := by
    have h1 : Real.sqrt n * |v x| = |∑ i : Fin n, eps x i * v (flipAt x i)| := by
      have : (∑ i : Fin n, eps x i * v (flipAt x i)) = Real.sqrt n * v x := by
        have := congrFun heig x
        simpa using this
      rw [this, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h2 : |∑ i : Fin n, eps x i * v (flipAt x i)| ≤ ∑ i : Fin n, |v (flipAt x i)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl (fun i _ => by rw [abs_mul, habs i, one_mul])
    have h3 : (∑ i : Fin n, |v (flipAt x i)|) = ∑ i ∈ F, |v (flipAt x i)| := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro i _ hi
      have : flipAt x i ∉ S := by simpa [hF] using hi
      rw [hsupp _ this, abs_zero]
    have h4 : (∑ i ∈ F, |v (flipAt x i)|) ≤ (F.card : ℝ) * |v x| := by
      calc (∑ i ∈ F, |v (flipAt x i)|) ≤ ∑ _i ∈ F, |v x| :=
            Finset.sum_le_sum (fun i _ => hx _)
        _ = (F.card : ℝ) * |v x| := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1]
    exact (h2.trans (le_of_eq h3)).trans h4
  exact le_of_mul_le_mul_right (by linarith) hvx

end Huang

section Sensitivity

variable {n : ℕ}

/-- The local sensitivity of `f` at `x`. -/
def sens (f : Q n → Bool) (x : Q n) : ℕ :=
  (univ.filter (fun i : Fin n => f (flipAt x i) ≠ f x)).card

/-- The sensitivity of a Boolean function. -/
def sensitivity (f : Q n → Bool) : ℕ := univ.sup (sens f)

/-- The parity (Hamming weight mod 2) of a hypercube vertex. -/
def par (x : Q n) : Bool := decide (Odd (univ.filter (fun j => x j = true)).card)

lemma par_eq_true_iff (x : Q n) : par x = true ↔ sgn x = -1 := by
  have h : cnt (fun _ : Fin n => True) x = (univ.filter (fun j => x j = true)).card := by
    unfold cnt; congr 1; apply Finset.filter_congr; intro k _; simp
  constructor
  · intro hp
    have hodd : Odd (univ.filter (fun j => x j = true)).card := by simpa [par] using hp
    simp [sgn, sgnp, h, Odd.neg_one_pow hodd]
  · intro hs
    by_contra hp
    have hev : ¬ Odd (univ.filter (fun j => x j = true)).card := by simpa [par] using hp
    rw [Nat.not_odd_iff_even] at hev
    rw [sgn, sgnp, h, Even.neg_one_pow hev] at hs
    norm_num at hs

lemma par_flipAt (x : Q n) (i : Fin n) : par (flipAt x i) ≠ par x := by
  intro h
  have hs : sgn (flipAt x i) = - sgn x := sgn_flipAt x i
  have hcases : sgn x = 1 ∨ sgn x = -1 := mul_self_eq_one_iff.1 (sgn_mul_self x)
  rcases hcases with h1 | h1
  · have hp : par x = false := by
      by_contra hp
      have := (par_eq_true_iff x).1 (by simpa using hp)
      rw [h1] at this; norm_num at this
    have hp' : par (flipAt x i) = false := by rw [h, hp]
    have : sgn (flipAt x i) = 1 := by
      rcases mul_self_eq_one_iff.1 (sgn_mul_self (flipAt x i)) with h2 | h2
      · exact h2
      · exact absurd ((par_eq_true_iff (flipAt x i)).2 h2) (by simp [hp'])
    rw [hs, h1] at this; norm_num at this
  · have hp : par x = true := (par_eq_true_iff x).2 h1
    have hp' : par (flipAt x i) = true := by rw [h, hp]
    have : sgn (flipAt x i) = -1 := (par_eq_true_iff _).1 hp'
    rw [hs, h1] at this; norm_num at this

/-- **Huang's sensitivity theorem**, combinatorial form: if the set of points where a
Boolean function `f` differs from the parity function does not have exactly half of the
`2^n` points of the cube, then the sensitivity of `f` is at least `√n`. -/
theorem huang_sensitivity_of_card_ne (hn : 1 ≤ n) (f : Q n → Bool)
    (hf : (univ.filter (fun x => f x ≠ par x)).card ≠ 2 ^ (n - 1)) :
    Real.sqrt n ≤ sensitivity f := by
  classical
  set S : Finset (Q n) := univ.filter (fun x => f x ≠ par x) with hSdef
  have hcardQ : Fintype.card (Q n) = 2 ^ n := by simp
  have hcompl : S.card + Sᶜ.card = 2 ^ n := by
    rw [Finset.card_compl, hcardQ]
    have : S.card ≤ 2 ^ n := by
      simpa [hcardQ] using (Finset.card_le_univ S)
    omega
  have hpow : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  -- choose the fibre of `f ⊕ par` which is larger than half of the cube
  obtain ⟨T, hTcard, hTsame⟩ :
      ∃ T : Finset (Q n), 2 ^ (n - 1) < T.card ∧
        ∀ x ∈ T, ∀ i : Fin n, flipAt x i ∈ T → f (flipAt x i) ≠ f x := by
    rcases lt_or_gt_of_ne hf with hlt | hgt
    · refine ⟨Sᶜ, by omega, ?_⟩
      intro x hx i hy
      have hx' : f x = par x := by
        by_contra hc
        exact (Finset.mem_compl.1 hx) (by simp [hSdef, hc])
      have hy' : f (flipAt x i) = par (flipAt x i) := by
        by_contra hc
        exact (Finset.mem_compl.1 hy) (by simp [hSdef, hc])
      have hpar := par_flipAt x i
      rw [hx', hy']
      exact hpar
    · refine ⟨S, hgt, ?_⟩
      intro x hx i hy
      have hx' : f x ≠ par x := by simpa [hSdef] using hx
      have hy' : f (flipAt x i) ≠ par (flipAt x i) := by simpa [hSdef] using hy
      have hpar := par_flipAt x i
      revert hx' hy' hpar
      cases f x <;> cases f (flipAt x i) <;> cases par x <;> cases par (flipAt x i) <;> simp
  obtain ⟨x, hxT, hx⟩ := huang_cube hn T hTcard
  refine hx.trans ?_
  have hsub : univ.filter (fun i : Fin n => flipAt x i ∈ T)
      ⊆ univ.filter (fun i : Fin n => f (flipAt x i) ≠ f x) := by
    intro i hi
    have : flipAt x i ∈ T := by simpa using hi
    simp [hTsame x hxT i this]
  have h1 : (univ.filter (fun i : Fin n => flipAt x i ∈ T)).card ≤ sens f x :=
    Finset.card_le_card hsub
  have h2 : sens f x ≤ sensitivity f := Finset.le_sup (Finset.mem_univ x)
  exact_mod_cast h1.trans h2

end Sensitivity

end Frontier

