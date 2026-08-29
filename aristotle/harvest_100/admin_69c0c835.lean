import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

set_option grind.warning false

/-!
## The cap set problem

We prove the Croot–Lev–Pach / Ellenberg–Gijswijt bound: a subset of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression has size `o(3ⁿ)`.
-/

namespace CapSet

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Points of `𝔽₃ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ZMod 3

/-- Exponent vectors of reduced monomials (each exponent is `0`, `1` or `2`). -/
abbrev Exp (n : ℕ) := Fin n → Fin 3

/-- The monomial function `x ↦ ∏ i, x i ^ α i` on `𝔽₃ⁿ`. -/
def mono {n : ℕ} (α : Exp n) : Pt n → ZMod 3 := fun x => ∏ i, x i ^ (α i : ℕ)

/-- Total degree of an exponent vector. -/
def edeg {n : ℕ} (α : Exp n) : ℕ := ∑ i, (α i : ℕ)

/-- Exponent vectors of total degree at most `d`. -/
def Dset (n d : ℕ) : Finset (Exp n) := Finset.univ.filter (fun α => edeg α ≤ d)

/-- The number of reduced monomials in `n` variables of total degree at most `d`. -/
def mcount (n d : ℕ) : ℕ := (Dset n d).card

/-- The space of (reduced) polynomial functions of total degree at most `d`. -/
def polySpace (n d : ℕ) : Submodule (ZMod 3) (Pt n → ZMod 3) :=
  Submodule.span (ZMod 3) (mono '' (Dset n d : Set (Exp n)))

lemma mem_Dset {n d : ℕ} {α : Exp n} : α ∈ Dset n d ↔ edeg α ≤ d := by
  simp [Dset]

/-! ### Monomials form a basis of the space of all functions -/

/-- Coefficients expressing the indicator of a point as a combination of monomials. -/
def cc (v : ZMod 3) (b : Fin 3) : ZMod 3 := ![1 - v ^ 2, 2 * v, -1] b

lemma cc_expand : ∀ (v x : ZMod 3), 1 - (x - v) ^ 2 = ∑ b : Fin 3, cc v b * x ^ (b : ℕ) := by
  decide

lemma sub_sq_eq_one {a b : ZMod 3} (h : a ≠ b) : (1 : ZMod 3) - (a - b) ^ 2 = 0 := by
  revert h; revert a b; decide

/-- The indicator function of the point `v`, written as a product. -/
lemma delta_eq {n : ℕ} (v x : Pt n) :
    (∏ i, (1 - (x i - v i) ^ 2)) = if x = v then 1 else 0 := by
  by_cases h : x = v
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ v i := by
      by_contra hc
      exact h (funext fun i => not_not.1 (fun hh => hc ⟨i, hh⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_sq_eq_one hi)

/-- The indicator of a point is a linear combination of monomials. -/
lemma delta_mem_span {n : ℕ} (v : Pt n) :
    (fun x => if x = v then (1 : ZMod 3) else 0) ∈
      Submodule.span (ZMod 3) (Set.range (mono (n := n))) := by
  have expand : (fun x : Pt n => if x = v then (1 : ZMod 3) else 0)
      = ∑ α : Exp n, (∏ i, cc (v i) (α i)) • mono α := by
    funext x
    rw [← delta_eq v x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mono]
    calc ∏ i, (1 - (x i - v i) ^ 2) = ∏ i, ∑ b : Fin 3, cc (v i) b * x i ^ (b : ℕ) :=
          Finset.prod_congr rfl fun i _ => cc_expand (v i) (x i)
      _ = ∑ α : Exp n, ∏ i, cc (v i) (α i) * x i ^ (α i : ℕ) := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      _ = ∑ α : Exp n, (∏ i, cc (v i) (α i)) * ∏ i, x i ^ (α i : ℕ) :=
          Finset.sum_congr rfl fun α _ => Finset.prod_mul_distrib
  rw [expand]
  exact Submodule.sum_mem _ fun α _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

lemma mono_span_top (n : ℕ) :
    ⊤ ≤ Submodule.span (ZMod 3) (Set.range (mono (n := n))) := by
  intro f _
  have hf : f = ∑ v : Pt n, f v • (fun x => if x = v then (1 : ZMod 3) else 0) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single x] <;> simp +contextual [eq_comm]
  rw [hf]
  exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (delta_mem_span v)

lemma mono_linearIndependent (n : ℕ) :
    LinearIndependent (ZMod 3) (mono (n := n)) := by
  have hcard : Fintype.card (Exp n) = Module.finrank (ZMod 3) (Pt n → ZMod 3) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hb := (basisOfTopLeSpanOfCardEqFinrank mono (mono_span_top n) hcard).linearIndependent
  rwa [coe_basisOfTopLeSpanOfCardEqFinrank] at hb

lemma finrank_polySpace (n d : ℕ) :
    Module.finrank (ZMod 3) (polySpace n d) = mcount n d := by
  have hli : LinearIndependent (ZMod 3) (fun α : {x // x ∈ Dset n d} => mono (α : Exp n)) :=
    (mono_linearIndependent n).comp _ Subtype.val_injective
  have hrange : Set.range (fun α : {x // x ∈ Dset n d} => mono (α : Exp n))
      = mono '' (Dset n d : Set (Exp n)) := by
    ext p
    simp [Set.mem_range, Set.mem_image]
  have h := finrank_span_eq_card hli
  rw [hrange] at h
  rw [polySpace, h, mcount, Fintype.card_coe]

/-! ### A subspace of functions contains a function with large support -/

lemma exists_large_support {V : Type} [Fintype V] [DecidableEq V]
    (W : Submodule (ZMod 3) (V → ZMod 3)) :
    ∃ f ∈ W, Module.finrank (ZMod 3) W ≤ #{v | f v ≠ 0} := by
  obtain ⟨F, -, hFmax⟩ := Finset.exists_max_image (Finset.univ : Finset W)
    (fun g => (Finset.univ.filter (fun v => (g : V → ZMod 3) v ≠ 0)).card) ⟨0, Finset.mem_univ _⟩
  refine ⟨(F : V → ZMod 3), F.2, ?_⟩
  set f : V → ZMod 3 := (F : V → ZMod 3) with hf
  set S : Finset V := Finset.univ.filter (fun v => f v ≠ 0) with hS
  have hmem : ∀ v, v ∈ S ↔ f v ≠ 0 := by intro v; simp [hS]
  let L : W →ₗ[ZMod 3] (↑(S : Set V) → ZMod 3) :=
    (LinearMap.funLeft (ZMod 3) (ZMod 3) (fun v : ↑(S : Set V) => (v : V))).comp W.subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro g hg
    have hg0 : ∀ v ∈ S, (g : V → ZMod 3) v = 0 := by
      intro v hv
      have := congrFun (LinearMap.mem_ker.1 hg) ⟨v, by simpa using hv⟩
      simpa [L, LinearMap.funLeft] using this
    by_contra hne
    obtain ⟨w, hw⟩ : ∃ w, (g : V → ZMod 3) w ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (Subtype.ext (funext hc))
    have hwS : w ∉ S := fun h => hw (hg0 w h)
    have hfw : f w = 0 := by
      by_contra h
      exact hwS ((hmem w).2 h)
    set T : Finset V := Finset.univ.filter (fun v => (f + (g : V → ZMod 3)) v ≠ 0) with hT
    have hsub : S ⊂ T := by
      refine ⟨fun v hv => ?_, fun hcon => ?_⟩
      · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        have hz : (f + (g : V → ZMod 3)) v = f v := by simp [hg0 v hv]
        rw [hz]
        exact (hmem v).1 hv
      · exact hwS (hcon (Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [hfw] using hw⟩))
    have hcard : #S < #T := Finset.card_lt_card hsub
    have hle := hFmax ⟨f + (g : V → ZMod 3), Submodule.add_mem _ F.2 g.2⟩ (Finset.mem_univ _)
    simp only [hT, hS] at hcard hle
    omega
  have h1 : Module.finrank (ZMod 3) W ≤ Module.finrank (ZMod 3) (↑(S : Set V) → ZMod 3) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card] at h1
  simpa using h1

/-! ### Expansion of a monomial at a sum -/

/-- One-variable binomial coefficients for the reduced monomial calculus over `𝔽₃`. -/
def kk (a b c : Fin 3) : ZMod 3 :=
  if (b : ℕ) + (c : ℕ) = (a : ℕ) then ((Nat.choose a b : ℕ) : ZMod 3) else 0

lemma kk_expand : ∀ (a : Fin 3) (x y : ZMod 3),
    (x + y) ^ (a : ℕ) = ∑ b : Fin 3, ∑ c : Fin 3, kk a b c * x ^ (b : ℕ) * y ^ (c : ℕ) := by
  decide

/-- Multivariate coefficient of `mono β x * mono γ y` in `mono α (x + y)`. -/
def KK {n : ℕ} (α β γ : Exp n) : ZMod 3 := ∏ i, kk (α i) (β i) (γ i)

lemma KK_ne_zero_deg {n : ℕ} {α β γ : Exp n} (h : KK α β γ ≠ 0) :
    edeg β + edeg γ = edeg α := by
  have hall : ∀ i, kk (α i) (β i) (γ i) ≠ 0 := fun i hi =>
    h (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hcoord : ∀ i, (β i : ℕ) + (γ i : ℕ) = (α i : ℕ) := by
    intro i
    by_contra hc
    exact hall i (by simp [kk, hc])
  simp only [edeg, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hcoord i

lemma mono_add_expand {n : ℕ} (α : Exp n) (x y : Pt n) :
    mono α (x + y) = ∑ β : Exp n, ∑ γ : Exp n, KK α β γ * mono β x * mono γ y := by
  have step1 : mono α (x + y)
      = ∏ i, ∑ p : Fin 3 × Fin 3, kk (α i) p.1 p.2 * x i ^ (p.1 : ℕ) * y i ^ (p.2 : ℕ) := by
    simp only [mono, Pi.add_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [kk_expand (α i) (x i) (y i), Fintype.sum_prod_type]
  have step2 : ∑ β : Exp n, ∑ γ : Exp n, KK α β γ * mono β x * mono γ y
      = ∑ q : Exp n × Exp n, KK α q.1 q.2 * mono q.1 x * mono q.2 y := by
    rw [Fintype.sum_prod_type]
  rw [step1, step2, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Fintype.sum_equiv
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin 3) (fun _ => Fin 3)) _ _ ?_
  intro P
  simp only [Equiv.arrowProdEquivProdArrow_apply, KK, mono]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-! ### The splitting lemma -/

/-- If `P` has degree at most `d ≤ 2e+1`, then `P (x + y)` splits into a part where the
`x`-monomials have degree at most `e` and a part where the `y`-monomials do. -/
lemma exists_split {n : ℕ} (d e : ℕ) (hde : d ≤ 2 * e + 1) (P : Pt n → ZMod 3)
    (hP : P ∈ polySpace n d) :
    ∃ q c : Exp n → (Pt n → ZMod 3), ∀ x y : Pt n,
      P (x + y) = (∑ β ∈ Dset n e, mono β x * q β y) + ∑ γ ∈ Dset n e, c γ x * mono γ y := by
  induction hP using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨α, hα, rfl⟩ := hf
      have hαd : edeg α ≤ d := mem_Dset.1 (by simpa using hα)
      refine ⟨fun β y => ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono γ y,
              fun γ x => ∑ β : Exp n, KK α β γ * mono β x, ?_⟩
      intro x y
      have hsplit : ∀ β : Exp n, (∑ γ : Exp n, KK α β γ * mono β x * mono γ y)
          = (∑ γ ∈ Dset n e, KK α β γ * mono β x * mono γ y)
            + ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono β x * mono γ y :=
        fun β => (Finset.sum_add_sum_compl _ _).symm
      have hA : (∑ β : Exp n, ∑ γ ∈ Dset n e, KK α β γ * mono β x * mono γ y)
          = ∑ γ ∈ Dset n e, (∑ β : Exp n, KK α β γ * mono β x) * mono γ y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [Finset.sum_mul]
      have hB : (∑ β : Exp n, ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono β x * mono γ y)
          = ∑ β ∈ Dset n e, mono β x * ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono γ y := by
        rw [← Finset.sum_add_sum_compl (Dset n e)
          (fun β => ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono β x * mono γ y)]
        have hzero : (∑ β ∈ (Dset n e)ᶜ, ∑ γ ∈ (Dset n e)ᶜ,
            KK α β γ * mono β x * mono γ y) = 0 := by
          refine Finset.sum_eq_zero fun β hβ => Finset.sum_eq_zero fun γ hγ => ?_
          have hβd : ¬ (edeg β ≤ e) := fun h => (Finset.mem_compl.1 hβ) (mem_Dset.2 h)
          have hγd : ¬ (edeg γ ≤ e) := fun h => (Finset.mem_compl.1 hγ) (mem_Dset.2 h)
          have hK : KK α β γ = 0 := by
            by_contra hK
            have := KK_ne_zero_deg hK
            omega
          simp [hK]
        rw [hzero, add_zero]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun γ _ => by ring
      rw [mono_add_expand α x y, Finset.sum_congr rfl (fun β _ => hsplit β),
        Finset.sum_add_distrib, hA, hB, add_comm]
  | zero => exact ⟨0, 0, by intro x y; simp⟩
  | add f g hf hg ihf ihg =>
      obtain ⟨q1, c1, h1⟩ := ihf
      obtain ⟨q2, c2, h2⟩ := ihg
      refine ⟨q1 + q2, c1 + c2, fun x y => ?_⟩
      simp only [Pi.add_apply, h1 x y, h2 x y, mul_add, add_mul, Finset.sum_add_distrib]
      ring
  | smul a f hf ih =>
      obtain ⟨q, c, h⟩ := ih
      refine ⟨fun β => a • q β, fun γ => a • c γ, fun x y => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, h x y, mul_add, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### Counting monomials -/

/-- Reversing all exponents (`a ↦ 2 - a`) complements the total degree. -/
lemma edeg_rev {n : ℕ} (α : Exp n) : edeg (fun i => 2 - α i) + edeg α = 2 * n := by
  have h : ∀ a : Fin 3, ((2 - a : Fin 3) : ℕ) + (a : ℕ) = 2 := by decide
  simp only [edeg, ← Finset.sum_add_distrib, h]
  simp [mul_comm]

/-- Complementary counting for monomial degrees. -/
lemma pow_le_mcount_add {n d e : ℕ} (h : d + e + 1 = 2 * n) :
    3 ^ n ≤ mcount n d + mcount n e := by
  have hsub : (Finset.univ : Finset (Exp n)) ⊆
      Dset n d ∪ (Dset n e).image (fun α i => 2 - α i) := by
    intro α _
    rcases le_or_gt (edeg α) d with hd | hd
    · exact Finset.mem_union_left _ (mem_Dset.2 hd)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨fun i => 2 - α i, mem_Dset.2 ?_, ?_⟩)
      · have := edeg_rev α; omega
      · funext i
        have h2 : ∀ a : Fin 3, 2 - (2 - a) = a := by decide
        exact h2 (α i)
  calc (3 : ℕ) ^ n = (Finset.univ : Finset (Exp n)).card := by simp
    _ ≤ (Dset n d ∪ (Dset n e).image (fun α i => 2 - α i)).card := Finset.card_le_card hsub
    _ ≤ (Dset n d).card + ((Dset n e).image (fun α i => 2 - α i)).card :=
        Finset.card_union_le _ _
    _ ≤ mcount n d + mcount n e := Nat.add_le_add_left Finset.card_image_le _
/-! ### The main combinatorial bound -/

lemma two_smul_eq_neg {n : ℕ} (a : Pt n) : a + a = -a := by
  funext i
  have : ∀ z : ZMod 3, z + z = -z := by decide
  simpa using this (a i)

/-- A subspace of a finite dimensional space meets the kernel of a linear map in a subspace of
codimension at most the dimension of the target. -/
lemma finrank_inf_ker_ge {V W : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] (S : Submodule (ZMod 3) V) (f : V →ₗ[ZMod 3] W) :
    Module.finrank (ZMod 3) S ≤
      Module.finrank (ZMod 3) (S ⊓ LinearMap.ker f : Submodule (ZMod 3) V)
        + Module.finrank (ZMod 3) W := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict S)
  have h1 : Module.finrank (ZMod 3) (LinearMap.range (f.domRestrict S))
      ≤ Module.finrank (ZMod 3) W := Submodule.finrank_le _
  have h2 : Module.finrank (ZMod 3) (LinearMap.ker (f.domRestrict S))
      = Module.finrank (ZMod 3) (S ⊓ LinearMap.ker f : Submodule (ZMod 3) V) := by
    rw [LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker f)),
      Submodule.map_comap_subtype]
  omega

/-- The Croot–Lev–Pach / Ellenberg–Gijswijt bound. -/
theorem card_le_three_mul_mcount (n : ℕ) (hn : 1 ≤ n) (A : Finset (Pt n))
    (hA : ThreeAPFree (A : Set (Pt n))) : A.card ≤ 3 * mcount n (2 * n / 3) := by
  set e := 2 * n / 3 with he
  set d := 2 * n - e - 1 with hdd
  have harith1 : d + e + 1 = 2 * n := by omega
  have harith2 : d ≤ 2 * e + 1 := by omega
  set B : Finset (Pt n) := A.image (fun a => -a) with hB
  have hBcard : B.card = A.card := Finset.card_image_of_injective _ neg_injective
  -- the cap set property: sums of two distinct elements of `A` avoid `B`
  have hcap : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x + y ∉ B := by
    intro x hx y hy hxy hmem
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.1 hmem
    have hzz : x + y = z + z := by rw [← hzeq, two_smul_eq_neg]
    have h1 : x = z := hA (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hz) (Finset.mem_coe.2 hy) hzz
    have h2 : y = z := hA (Finset.mem_coe.2 hy) (Finset.mem_coe.2 hz) (Finset.mem_coe.2 hx)
      (by rw [add_comm]; exact hzz)
    exact hxy (h1.trans h2.symm)
  -- the space of polynomials of degree `≤ d` supported on `B`
  set fmap : (Pt n → ZMod 3) →ₗ[ZMod 3] ({v : Pt n // v ∈ Bᶜ} → ZMod 3) :=
    LinearMap.funLeft (ZMod 3) (ZMod 3) (fun v : {v : Pt n // v ∈ Bᶜ} => (v : Pt n)) with hfmap
  set W : Submodule (ZMod 3) (Pt n → ZMod 3) := polySpace n d ⊓ LinearMap.ker fmap with hW
  have hcodim : Module.finrank (ZMod 3) ({v : Pt n // v ∈ Bᶜ} → ZMod 3) = #(Bᶜ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hWrank : mcount n d ≤ Module.finrank (ZMod 3) W + #(Bᶜ) := by
    have h := finrank_inf_ker_ge (polySpace n d) fmap
    rw [finrank_polySpace, hcodim] at h
    exact h
  obtain ⟨P, hPW, hPsupp⟩ := exists_large_support W
  have hPpoly : P ∈ polySpace n d := hPW.1
  have hPvanish : ∀ v : Pt n, v ∉ B → P v = 0 := by
    intro v hv
    have := congrFun (LinearMap.mem_ker.1 hPW.2) ⟨v, Finset.mem_compl.2 hv⟩
    simpa [hfmap, LinearMap.funLeft] using this
  -- the set of `a ∈ A` where the polynomial does not vanish at `2a = -a`
  set S : Finset (Pt n) := A.filter (fun a => P (-a) ≠ 0) with hS
  have hsupp_le : #{v | P v ≠ 0} ≤ #S := by
    refine Finset.card_le_card_of_injOn (fun v => -v) ?_ ?_
    · intro v hv
      have hv0 : P v ≠ 0 := by simpa using (Finset.mem_filter.1 hv).2
      have hvB : v ∈ B := by
        by_contra hc
        exact hv0 (hPvanish v hc)
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 hvB
      refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · show -v ∈ A
        have hva : -v = a := by rw [← hae, neg_neg]
        rwa [hva]
      · show P (-(-v)) ≠ 0
        rwa [neg_neg]
    · intro u _ v _ h
      exact neg_injective h
  -- the functions `y ↦ P (a + y)` for `a ∈ S` are linearly independent
  have hPaa : ∀ a ∈ S, P (a + a) ≠ 0 := by
    intro a ha
    rw [two_smul_eq_neg]
    exact (Finset.mem_filter.1 ha).2
  have hPsum : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → P (x + y) = 0 := fun x hx y hy hxy =>
    hPvanish _ (hcap x hx y hy hxy)
  have hSA : S ⊆ A := Finset.filter_subset _ _
  have hindep : LinearIndependent (ZMod 3)
      (fun a : {x // x ∈ S} => (fun y => P ((a : Pt n) + y) : Pt n → ZMod 3)) := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf a
    have hev := congrFun hcf (a : Pt n)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
    rw [Finset.sum_eq_single a] at hev
    · exact (mul_eq_zero.1 hev).resolve_right (hPaa a a.2)
    · intro b _ hba
      have hne : (b : Pt n) ≠ (a : Pt n) := fun h => hba (Subtype.ext h)
      rw [hPsum (b : Pt n) (hSA b.2) (a : Pt n) (hSA a.2) hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  -- all these functions lie in a space of dimension at most `2 * mcount n e`
  obtain ⟨q, c, hqc⟩ := exists_split d e harith2 P hPpoly
  set fs : Finset (Pt n → ZMod 3) :=
    (Dset n e).image (fun β => q β) ∪ (Dset n e).image (fun γ => mono γ) with hfs
  set U : Submodule (ZMod 3) (Pt n → ZMod 3) := Submodule.span (ZMod 3) (fs : Set (Pt n → ZMod 3))
    with hU
  have hmemU : ∀ x : Pt n, (fun y => P (x + y)) ∈ U := by
    intro x
    have hrepr : (fun y => P (x + y))
        = (∑ β ∈ Dset n e, mono β x • q β) + ∑ γ ∈ Dset n e, c γ x • mono γ := by
      funext y
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hqc x y
    rw [hrepr]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun β hβ => ?_)
      (Submodule.sum_mem _ fun γ hγ => ?_)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by
        simp only [hfs, Finset.coe_union, Set.mem_union]
        exact Or.inl (by simpa using Finset.mem_image_of_mem (fun β => q β) hβ)))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by
        simp only [hfs, Finset.coe_union, Set.mem_union]
        exact Or.inr (by simpa using Finset.mem_image_of_mem (fun γ => mono γ) hγ)))
  have hScard : #S ≤ 2 * mcount n e := by
    have hindepU : LinearIndependent (ZMod 3)
        (fun a : {x // x ∈ S} => (⟨fun y => P ((a : Pt n) + y), hmemU (a : Pt n)⟩ : U)) := by
      refine LinearIndependent.of_comp U.subtype ?_
      exact hindep
    have h1 : Fintype.card {x // x ∈ S} ≤ Module.finrank (ZMod 3) U :=
      hindepU.fintype_card_le_finrank
    have h2 : Module.finrank (ZMod 3) U ≤ #fs := finrank_span_finset_le_card fs
    have h3 : #fs ≤ 2 * mcount n e := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have hb1 : ((Dset n e).image (fun β => q β)).card ≤ mcount n e := Finset.card_image_le
      have hb2 : ((Dset n e).image (fun γ => mono γ)).card ≤ mcount n e := Finset.card_image_le
      omega
    rw [Fintype.card_coe] at h1
    omega
  -- put everything together
  have hcompl : #(Bᶜ) + A.card = 3 ^ n := by
    have h := Finset.card_add_card_compl B
    have hcard : Fintype.card (Pt n) = 3 ^ n := by simp [Pt]
    omega
  have hpow : 3 ^ n ≤ mcount n d + mcount n e := pow_le_mcount_add harith1
  omega


lemma sum_half_pow_edeg (n : ℕ) :
    ∑ α : Exp n, (1 / 2 : ℝ) ^ (edeg α) = (7 / 4) ^ n := by
  have h3 : (∑ b : Fin 3, (1 / 2 : ℝ) ^ (b : ℕ)) = 7 / 4 := by
    simp [Fin.sum_univ_three]; norm_num
  have h : ((7 : ℝ) / 4) ^ n = ∏ _i : Fin n, ∑ b : Fin 3, (1 / 2 : ℝ) ^ (b : ℕ) := by
    rw [Finset.prod_const, h3, Finset.card_univ, Fintype.card_fin]
  rw [h, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [edeg, ← Finset.prod_pow_eq_pow_sum]

/-- A Chernoff-type bound on the number of low degree monomials. -/
lemma mcount_le (n e : ℕ) : (mcount n e : ℝ) ≤ 2 ^ e * (7 / 4) ^ n := by
  have key : (mcount n e : ℝ) * (1 / 2) ^ e ≤ (7 / 4) ^ n := by
    rw [← sum_half_pow_edeg n]
    calc (mcount n e : ℝ) * (1 / 2) ^ e = ∑ _α ∈ Dset n e, (1 / 2 : ℝ) ^ e := by
          rw [Finset.sum_const, mcount]; simp [mul_comm]
      _ ≤ ∑ α ∈ Dset n e, (1 / 2 : ℝ) ^ (edeg α) :=
          Finset.sum_le_sum fun α hα =>
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (mem_Dset.1 hα)
      _ ≤ ∑ α : Exp n, (1 / 2 : ℝ) ^ (edeg α) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
          intros; positivity
  have h2 : (0 : ℝ) < (1 / 2) ^ e := by positivity
  rw [← le_div_iff₀ h2] at key
  calc (mcount n e : ℝ) ≤ (7 / 4) ^ n / (1 / 2) ^ e := key
    _ = 2 ^ e * (7 / 4) ^ n := by
        rw [eq_comm, mul_comm, eq_div_iff (ne_of_gt h2), mul_assoc, ← mul_pow]
        norm_num

/-! ### Asymptotics -/

/-- The base `2^(2/3) * 7/4 ≈ 2.7756 < 3` of the exponential bound we obtain. -/
noncomputable def cbase : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 3) * (7 / 4)

lemma rpow_two_third_lt : (2 : ℝ) ^ ((2 : ℝ) / 3) < 12 / 7 := by
  have h3 : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = 4 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) < (12 / 7 : ℝ) ^ (3 : ℕ) := by
    rw [h3]; norm_num
  exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) h

lemma cbase_lt_three : cbase < 3 := by
  have h : (2 : ℝ) ^ ((2 : ℝ) / 3) * (7 / 4) < (12 / 7) * (7 / 4) :=
    mul_lt_mul_of_pos_right rpow_two_third_lt (by norm_num)
  simpa [cbase] using h.trans_le (by norm_num)

lemma cbase_nonneg : (0 : ℝ) ≤ cbase := by
  have h : (0 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
  unfold cbase; positivity

lemma pow_two_le (n : ℕ) : (2 : ℝ) ^ (2 * n / 3) ≤ ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ n := by
  rw [← Real.rpow_natCast (2 : ℝ) (2 * n / 3), ← Real.rpow_natCast ((2 : ℝ) ^ ((2 : ℝ) / 3)) n,
    ← Real.rpow_mul (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h : 2 * n / 3 * 3 ≤ 2 * n := Nat.div_mul_le_self _ _
  have h' : ((2 * n / 3 : ℕ) : ℝ) * 3 ≤ 2 * (n : ℝ) := by exact_mod_cast h
  linarith

lemma three_mul_mcount_le_cbase (n : ℕ) :
    ((3 * mcount n (2 * n / 3) : ℕ) : ℝ) ≤ 3 * cbase ^ n := by
  have h := mcount_le n (2 * n / 3)
  have hpos : (0 : ℝ) ≤ (7 / 4 : ℝ) ^ n := by positivity
  have h2 : (2 : ℝ) ^ (2 * n / 3) * (7 / 4) ^ n ≤ ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ n * (7 / 4) ^ n :=
    mul_le_mul_of_nonneg_right (pow_two_le n) hpos
  have hc : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ n * (7 / 4) ^ n = cbase ^ n := by
    rw [cbase, mul_pow]
  push_cast
  nlinarith [h, h2, hc]

/-- The exponential form of the cap set bound. -/
lemma card_le_cbase (n : ℕ) (hn : 1 ≤ n) (A : Finset (Pt n))
    (hA : ThreeAPFree (A : Set (Pt n))) : (A.card : ℝ) ≤ 3 * cbase ^ n := by
  have h1 : (A.card : ℝ) ≤ ((3 * mcount n (2 * n / 3) : ℕ) : ℝ) := by
    exact_mod_cast card_le_three_mul_mcount n hn A hA
  exact h1.trans (three_mul_mcount_le_cbase n)

/-- The largest size of a 3AP-free subset of `𝔽₃ⁿ`. -/
noncomputable def capSetMax (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Finset (Pt n))).sup
    (fun A : Finset (Pt n) => if ThreeAPFree (A : Set (Pt n)) then A.card else 0)

lemma capSetMax_le (n : ℕ) (hn : 1 ≤ n) : capSetMax n ≤ 3 * mcount n (2 * n / 3) := by
  refine Finset.sup_le fun A _ => ?_
  by_cases h : ThreeAPFree (A : Set (Pt n))
  · simpa [h] using card_le_three_mul_mcount n hn A h
  · simp [h]

lemma capSetMax_le_cbase (n : ℕ) (hn : 1 ≤ n) : (capSetMax n : ℝ) ≤ 3 * cbase ^ n := by
  have h1 : (capSetMax n : ℝ) ≤ ((3 * mcount n (2 * n / 3) : ℕ) : ℝ) := by
    exact_mod_cast capSetMax_le n hn
  exact h1.trans (three_mul_mcount_le_cbase n)

/-- The uniform `ε`-`N` form of the cap set bound, for any family bounded by `3 * cbase ^ n`. -/
lemma eventually_le_eps {f : ℕ → ℝ} (H : ∀ n : ℕ, 1 ≤ n → f n ≤ 3 * cbase ^ n)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≤ ε * 3 ^ n := by
  have hq : |cbase / 3| < 1 := by
    rw [abs_of_nonneg (div_nonneg cbase_nonneg (by norm_num))]
    linarith [cbase_lt_three]
  have hlim : Filter.Tendsto (fun n : ℕ => 3 * (cbase / 3) ^ n) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
    simpa using h.const_mul (3 : ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually_le_const hε)
  refine ⟨max N 1, fun n hn => ?_⟩
  have h1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have h2 : N ≤ n := le_trans (le_max_left N 1) hn
  have key : 3 * cbase ^ n = (3 * (cbase / 3) ^ n) * 3 ^ n := by
    rw [div_pow]; field_simp
  calc f n ≤ 3 * cbase ^ n := H n h1
    _ = (3 * (cbase / 3) ^ n) * 3 ^ n := key
    _ ≤ ε * 3 ^ n := mul_le_mul_of_nonneg_right (hN n h2) (by positivity)

/-- A sanity check: the four-element cap in `𝔽₃²`, showing the hypothesis is satisfiable. -/
example : ThreeAPFree (({![0, 0], ![0, 1], ![1, 0], ![1, 1]} : Finset (Pt 2)) : Set (Pt 2)) := by
  decide

end CapSet

namespace Math2

/-- **Cap set theorem** (Croot–Lev–Pach, Ellenberg–Gijswijt): subsets of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression have size `o(3ⁿ)`. -/
theorem cap_set : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Finset (CapSet.Pt n), ThreeAPFree (A : Set (CapSet.Pt n)) →
      (A.card : ℝ) ≤ ε * 3 ^ n := by
  intro ε hε
  obtain ⟨N, hN⟩ :=
    CapSet.eventually_le_eps (f := fun n => 3 * CapSet.cbase ^ n) (fun _ _ => le_rfl) hε
  refine ⟨max N 1, fun n hn A hA => ?_⟩
  exact (CapSet.card_le_cbase n (le_trans (le_max_right N 1) hn) A hA).trans
    (hN n (le_trans (le_max_left N 1) hn))

/-- The cap set theorem in little-o form. -/
theorem cap_set_isLittleO :
    (fun n : ℕ => (CapSet.capSetMax n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (3 : ℝ) ^ n) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := CapSet.eventually_le_eps CapSet.capSetMax_le_cbase hε
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact hN n hn

end Math2

