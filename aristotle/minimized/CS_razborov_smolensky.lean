import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/

theorem induction {P : Circuit → Prop}
    (hvar : ∀ i, P (.var i)) (hconst : ∀ b, P (.const b))
    (hnot : ∀ c, P c → P c.cnot)
    (hor : ∀ cs, (∀ c ∈ cs, P c) → P (.cor cs))
    (hand : ∀ cs, (∀ c ∈ cs, P c) → P (.cand cs))
    (hmod : ∀ cs, (∀ c ∈ cs, P c) → P (.cmod cs)) : ∀ c, P c := by
  intro c
  induction c using Circuit.rec (motive_2 := fun cs => ∀ c ∈ cs, P c) with
  | var i => exact hvar i
  | const b => exact hconst b
  | cnot c ih => exact hnot c ih
  | cor cs ih => exact hor cs ih
  | cand cs ih => exact hand cs ih
  | cmod cs ih => exact hmod cs ih
  | nil => rename_i d hd; simp at hd
  | cons c cs ih ihs =>
      rename_i d hd
      rcases List.mem_cons.1 hd with h | h
      · subst h; exact ih
      · exact ihs d h

/-- The number of gates of a circuit. -/

def bitv (b : Bool) : F := if b then 1 else 0

def mon {n : ℕ} (S : Finset (Fin n)) : Cube n → F := fun x => ∏ i ∈ S, bitv F (x i)

theorem mon_eq_ite {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    (mon S : Cube n → F) x = if ∀ i ∈ S, x i = true then 1 else 0 := by
  unfold mon
  split
  · rename_i h
    exact Finset.prod_eq_one fun i hi => by simp [h i hi]
  · rename_i h
    push_neg at h
    obtain ⟨i, hi, hx⟩ := h
    refine Finset.prod_eq_zero hi ?_
    have hxf : x i = false := by simpa using hx
    simp [hxf]

theorem mon_mul_mon {n : ℕ} (S T : Finset (Fin n)) :
    (mon S : Cube n → F) * mon T = mon (S ∪ T) := by
  funext x
  simp only [Pi.mul_apply, mon_eq_ite]
  by_cases hS : ∀ i ∈ S, x i = true <;> by_cases hT : ∀ i ∈ T, x i = true <;>
    simp_all [Finset.mem_union] <;> grind

variable (F)

/-- The set of monomials of degree at most `d`. -/

def monsSet (n d : ℕ) : Set (Cube n → F) := (fun S => (mon S : Cube n → F)) '' {S | S.card ≤ d}

theorem monsSet_finite (n d : ℕ) : (monsSet F n d).Finite :=
  Set.Finite.image _ (Set.toFinite _)

/-- Functions on the cube computed by polynomials of degree at most `d`. -/

def Deg (n d : ℕ) : Submodule F (Cube n → F) := Submodule.span F (monsSet F n d)

variable {F}

theorem mon_mem_Deg {n d : ℕ} {S : Finset (Fin n)} (h : S.card ≤ d) :
    (mon S : Cube n → F) ∈ Deg F n d :=
  Submodule.subset_span ⟨S, h, rfl⟩

theorem Deg_mono {n : ℕ} {d e : ℕ} (h : d ≤ e) : Deg F n d ≤ Deg F n e := by
  apply Submodule.span_mono
  rintro _ ⟨S, hS, rfl⟩
  exact ⟨S, le_trans hS h, rfl⟩

theorem mem_Deg_of_le {n d e : ℕ} {f : Cube n → F} (hf : f ∈ Deg F n d) (h : d ≤ e) :
    f ∈ Deg F n e := Deg_mono h hf

theorem one_mem_Deg {n d : ℕ} : (1 : Cube n → F) ∈ Deg F n d := by
  have := mon_mem_Deg (F := F) (n := n) (d := d) (S := ∅) (by simp)
  simpa using this

theorem const_mem_Deg {n d : ℕ} (c : F) : (fun _ : Cube n => c) ∈ Deg F n d := by
  have h : (fun _ : Cube n => c) = c • (1 : Cube n → F) := by funext x; simp
  rw [h]
  exact Submodule.smul_mem _ _ one_mem_Deg

theorem mul_mem_Deg {n d e : ℕ} {f g : Cube n → F} (hf : f ∈ Deg F n d) (hg : g ∈ Deg F n e) :
    f * g ∈ Deg F n (d + e) := by
  have h1 : Deg F n d * Deg F n e ≤ Deg F n (d + e) := by
    rw [Deg, Deg, Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ⟨S, hS, rfl⟩, b, ⟨T, hT, rfl⟩, rfl⟩
    show (mon S : Cube n → F) * mon T ∈ Deg F n (d + e)
    rw [mon_mul_mon]
    exact mon_mem_Deg (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hS hT))
  exact h1 (Submodule.mul_mem_mul hf hg)

theorem prod_mem_Deg {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Cube n → F) (d : ℕ)
    (hf : ∀ i ∈ s, f i ∈ Deg F n d) : (∏ i ∈ s, f i) ∈ Deg F n (s.card * d) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_Deg
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : f a ∈ Deg F n d := hf a (by simp)
      have h2 : (∏ i ∈ s, f i) ∈ Deg F n (s.card * d) :=
        ih fun i hi => hf i (by simp [hi])
      have := mul_mem_Deg h1 h2
      exact mem_Deg_of_le this (by ring_nf; omega)

theorem bit_var_mem_Deg {n : ℕ} (i : Fin n) :
    (fun x : Cube n => bitv F (x i)) ∈ Deg F n 1 := by
  have h := mon_mem_Deg (F := F) (S := ({i} : Finset (Fin n))) (d := 1) (by simp)
  have he : (fun x : Cube n => bitv F (x i)) = (mon ({i} : Finset (Fin n)) : Cube n → F) := by
    funext x; simp [mon]
  rw [he]; exact h

open Classical in
/-- The set of points where `P` fails to compute the Boolean function `v`. -/

theorem card_filter_card_le (n d : ℕ) :
    #(Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)) ≤
      ∑ i ∈ Finset.range (d + 1), n.choose i := by
  classical
  have hsub : (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)) ⊆
      (Finset.range (d + 1)).biUnion (fun i => Finset.powersetCard i Finset.univ) := by
    intro S hS
    simp only [Finset.mem_filter] at hS
    exact Finset.mem_biUnion.2 ⟨S.card, by simp [hS.2],
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_biUnion_le) ?_)
  refine Finset.sum_le_sum fun i _ => ?_
  simp [Finset.card_powersetCard]

theorem finrank_Deg_le (n d : ℕ) :
    Module.finrank F (Deg F n d) ≤ ∑ i ∈ Finset.range (d + 1), n.choose i := by
  classical
  haveI : Fintype (monsSet F n d) := (monsSet_finite F n d).fintype
  refine le_trans (finrank_span_le_card (R := F) (monsSet F n d)) ?_
  have h1 : #(monsSet F n d).toFinset ≤ #(Finset.univ.filter
      (fun S : Finset (Fin n) => S.card ≤ d)) := by
    refine Finset.card_le_card_of_surjOn (fun S => (mon S : Cube n → F)) ?_
    intro f hf
    simp only [Finset.mem_coe, Set.mem_toFinset, monsSet] at hf
    obtain ⟨S, hS, rfl⟩ := hf
    exact ⟨S, by simpa using hS, rfl⟩
  exact le_trans h1 (card_filter_card_le n d)

instance instFiniteDeg (n d : ℕ) : Module.Finite F (Deg F n d) := by
  haveI : Fintype (monsSet F n d) := (monsSet_finite F n d).fintype
  exact Module.Finite.span_of_finite F (monsSet_finite F n d)

end CS

import RequestProject.CircuitApprox
import RequestProject.Smolensky

/-!
# Ingredients for the final assembly
-/

namespace CS

open Finset

/-! ### A polynomial is eventually dominated by `2 ^ k` -/

def ext {n : ℕ} (β : ℕ → Bool) (x : Cube n) : ℕ → Bool :=
  fun i => if h : i < n then x ⟨i, h⟩ else β i

def uu (ζ : F) (i : Fin n) : Cube n → F := fun x => 1 + (ζ - 1) * bitv F (x i)

/-- `ζ ^ (-x i)`, as a degree one function of `x`. -/

def vv (ζ : F) (i : Fin n) : Cube n → F := fun x => 1 + (ζ⁻¹ - 1) * bitv F (x i)

/-- The product `∏_{i ∈ S} ζ ^ (x i)`. -/

def UU (ζ : F) (S : Finset (Fin n)) : Cube n → F := ∏ i ∈ S, uu ζ i

theorem uu_mem_Deg (ζ : F) (i : Fin n) : uu ζ i ∈ Deg F n 1 := by
  have h : uu ζ i = (fun _ : Cube n => (1 : F)) + (ζ - 1) • (fun x : Cube n => bitv F (x i)) := by
    funext x; simp [uu, mul_comm]
  rw [h]
  exact Submodule.add_mem _ (const_mem_Deg _) (Submodule.smul_mem _ _ (bit_var_mem_Deg i))

theorem vv_mem_Deg (ζ : F) (i : Fin n) : vv ζ i ∈ Deg F n 1 := by
  have h : vv ζ i = (fun _ : Cube n => (1 : F)) + (ζ⁻¹ - 1) • (fun x : Cube n => bitv F (x i)) := by
    funext x; simp [vv, mul_comm]
  rw [h]
  exact Submodule.add_mem _ (const_mem_Deg _) (Submodule.smul_mem _ _ (bit_var_mem_Deg i))

theorem UU_mem_Deg (ζ : F) (S : Finset (Fin n)) : UU ζ S ∈ Deg F n S.card := by
  have := prod_mem_Deg (F := F) S (fun i => uu ζ i) 1 (fun i _ => uu_mem_Deg ζ i)
  simpa [UU] using this

theorem uu_mul_vv {ζ : F} (hζ : ζ ≠ 0) (i : Fin n) : uu ζ i * vv ζ i = 1 := by
  funext x
  cases h : x i
  · simp [uu, vv, h, bitv]
  · simp [uu, vv, h, bitv]; field_simp

/-- Splitting off the full product: `∏_{i∈S} u i = (∏_i u i) * ∏_{i ∉ S} v i`. -/

theorem UU_split {ζ : F} (hζ : ζ ≠ 0) (S : Finset (Fin n)) :
    UU ζ Finset.univ * (∏ i ∈ Sᶜ, vv ζ i) = UU ζ S := by
  classical
  have h1 : UU ζ Finset.univ = UU ζ S * ∏ i ∈ Sᶜ, uu ζ i := by
    rw [UU, UU, ← Finset.prod_union (disjoint_compl_right)]
    congr 1
    simp
  rw [h1, mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun i _ => uu_mul_vv hζ i), Finset.prod_const_one, mul_one]

/-- The indicator function of a point of the cube. -/

noncomputable def delta (y : Cube n) : Cube n → F :=
  fun x => ∏ i, (if y i then bitv F (x i) else 1 - bitv F (x i))

theorem delta_apply (y x : Cube n) : (delta y : Cube n → F) x = if x = y then 1 else 0 := by
  unfold delta
  split
  · rename_i h
    subst h
    refine Finset.prod_eq_one fun i _ => ?_
    cases h : x i <;> simp
  · rename_i h
    have : ∃ i, x i ≠ y i := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    obtain ⟨i, hi⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hy : y i <;> cases hx : x i <;> simp_all

/-- Each point indicator lies in the span of the products `∏_{i∈S} ζ^(x i)`. -/

theorem delta_mem_span {ζ : F} (hζ1 : ζ ≠ 1) (y : Cube n) :
    (delta y : Cube n → F) ∈ Submodule.span F (Set.range (UU ζ)) := by
  classical
  have hz : ζ - 1 ≠ 0 := sub_ne_zero_of_ne hζ1
  set a : Fin n → F := fun i => if y i then (ζ - 1)⁻¹ else -(ζ - 1)⁻¹ with ha
  set b : Fin n → F := fun i => if y i then -(ζ - 1)⁻¹ else ζ * (ζ - 1)⁻¹ with hb
  have hfac : (delta y : Cube n → F)
      = ∏ i, ((a i) • uu ζ i + (fun _ : Cube n => b i)) := by
    funext x
    simp only [delta, Finset.prod_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases hy : y i <;> cases hx : x i <;>
      simp [ha, hb, hy, hx, uu, bitv] <;> field_simp <;> ring
  rw [hfac, Finset.prod_add]
  refine Submodule.sum_mem _ fun T _ => ?_
  have hval : (∏ i ∈ T, (a i) • uu ζ i) * (∏ i ∈ Finset.univ \ T, (fun _ : Cube n => b i))
      = ((∏ i ∈ T, a i) * (∏ i ∈ Finset.univ \ T, b i)) • UU ζ T := by
    funext x
    simp only [Finset.prod_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, UU]
    rw [Finset.prod_mul_distrib]
    simp [mul_comm, mul_assoc]
  rw [hval]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)

theorem span_UU_eq_top {ζ : F} (hζ1 : ζ ≠ 1) :
    Submodule.span F (Set.range (UU ζ)) = (⊤ : Submodule F (Cube n → F)) := by
  classical
  refine top_le_iff.mp ?_
  rw [← (Pi.basisFun F (Cube n)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, rfl⟩
  have : (Pi.basisFun F (Cube n)) y = (delta y : Cube n → F) := by
    funext x
    rw [delta_apply]
    simp [Pi.basisFun_apply, Pi.single_apply]
  rw [this]
  exact delta_mem_span hζ1 y

/-- **Smolensky's dimension bound.** -/

theorem smolensky_dim {m D : ℕ} (hn : n = 2 * m) {ζ : F} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (A : Finset (Cube n)) (P : Cube n → F) (hP : P ∈ Deg F n D)
    (hPA : ∀ x ∈ A, UU ζ Finset.univ x = P x) :
    #A ≤ ∑ i ∈ Finset.range (m + D + 1), n.choose i := by
  classical
  set res : (Cube n → F) →ₗ[F] (↥A → F) :=
    LinearMap.funLeft F F (fun y : ↥A => (y : Cube n)) with hres
  have hressurj : Function.Surjective res :=
    LinearMap.funLeft_surjective_of_injective F F _ (fun y z h => Subtype.ext h)
  set W := Deg F n (m + D) with hW
  -- every `UU ζ S` restricts into the image of `W`
  have hUS : ∀ S : Finset (Fin n), res (UU ζ S) ∈ Submodule.map res W := by
    intro S
    by_cases hS : S.card ≤ m + D
    · exact Submodule.mem_map_of_mem (mem_Deg_of_le (UU_mem_Deg ζ S) hS)
    · have hSm : m < S.card := by omega
      have hcompl : Sᶜ.card ≤ m := by
        have : Sᶜ.card = n - S.card := by simp [Finset.card_compl]
        omega
      have hmem : P * (∏ i ∈ Sᶜ, vv ζ i) ∈ W := by
        refine mem_Deg_of_le (mul_mem_Deg hP
          (prod_mem_Deg (F := F) Sᶜ (fun i => vv ζ i) 1 (fun i _ => vv_mem_Deg ζ i))) ?_
        simp only [mul_one]
        omega
      refine ⟨P * (∏ i ∈ Sᶜ, vv ζ i), hmem, ?_⟩
      funext y
      have hy : (y : Cube n) ∈ A := y.2
      simp only [hres, LinearMap.funLeft_apply]
      rw [← UU_split hζ0 S]
      simp only [Pi.mul_apply]
      rw [hPA _ hy]
  have hmaptop : Submodule.map res W = ⊤ := by
    refine top_le_iff.mp ?_
    have h1 : Submodule.map res (⊤ : Submodule F (Cube n → F)) = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top.2 hressurj]
    rw [← h1, ← span_UU_eq_top hζ1, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨S, rfl⟩, rfl⟩
    exact hUS S
  have hfin : Module.finrank F (↥A → F) = #A := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  calc #A = Module.finrank F (↥A → F) := hfin.symm
    _ = Module.finrank F (Submodule.map res W) := by rw [hmaptop, finrank_top]
    _ ≤ Module.finrank F W := Submodule.finrank_map_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + D + 1), n.choose i := finrank_Deg_le n (m + D)

end CS

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

import Mathlib

/-!
# Binomial coefficient estimates

Two elementary facts used in the Razborov–Smolensky argument:

* the central binomial coefficient satisfies `C(2m,m)^2 * (3m+1) ≤ 16^m`
  (i.e. `C(2m,m) ≲ 4^m / √(3m)`);
* the partial sum `∑_{i ≤ m+D} C(2m,i)` is at most `4^m/2 + (D+1) C(2m,m)`.
-/

namespace CS

open Finset

/-- `C(2m,m)^2 (3m+1) ≤ 16^m`. -/
