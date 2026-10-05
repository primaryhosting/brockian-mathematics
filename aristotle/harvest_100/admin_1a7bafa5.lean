import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/
noncomputable def yMon (ζ : F) {n : ℕ} (S : Finset (Fin n)) : (Fin n → Bool) → F :=
  fun x => ∏ i ∈ S, (1 + (ζ - 1) * bv F (x i))

lemma yMon_apply (ζ : F) (S : Finset (Fin n)) (x : Fin n → Bool) :
    yMon ζ S x = ζ ^ ((S.filter (fun i => x i = true)).card) := by
  unfold yMon
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun i => x i = true)]
  have h1 : ∀ i ∈ S.filter (fun i => x i = true), (1 + (ζ - 1) * bv F (x i)) = ζ := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp [hi.2, bv]
  have h2 : ∀ i ∈ S.filter (fun i => ¬ (x i = true)), (1 + (ζ - 1) * bv F (x i)) = 1 := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp [Bool.eq_false_iff.mpr hi.2, bv]
  rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2]
  simp

lemma yMon_univ_apply (ζ : F) (x : Fin n → Bool) :
    yMon ζ (univ : Finset (Fin n)) x = ζ ^ (count x) := by
  rw [yMon_apply]; rfl

lemma yMon_mem_LD (ζ : F) (S : Finset (Fin n)) : yMon ζ S ∈ LD F n S.card := by
  have h : ∀ i ∈ S, (fun x : Fin n → Bool => 1 + (ζ - 1) * bv F (x i)) ∈ LD F n 1 := by
    intro i _
    refine Submodule.add_mem _ (one_mem_LD 1) ?_
    have : (fun x : Fin n → Bool => (ζ - 1) * bv F (x i))
        = (ζ - 1) • (fun x : Fin n → Bool => bv F (x i)) := by
      funext x; simp [smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (coord_mem_LD i 1 le_rfl)
  have h2 := prod_mem_LD S (fun i => (fun x : Fin n → Bool => 1 + (ζ - 1) * bv F (x i)))
    (fun _ => 1) h
  have heq : yMon ζ S = ∏ i ∈ S, (fun x : Fin n → Bool => 1 + (ζ - 1) * bv F (x i)) := by
    funext x; simp [yMon, Finset.prod_apply]
  rw [heq]
  simpa using h2

/-- The `y`-monomials span all functions on the cube. -/
lemma yMon_span {ζ : F} (hζ1 : ζ ≠ 1) :
    Submodule.span F (Set.range (yMon ζ (n := n))) = ⊤ := by
  rw [eq_top_iff, ← LD_top (F := F) (n := n), LD]
  refine Submodule.span_le.2 ?_
  intro g hg
  simp only [monFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hg
  obtain ⟨S, -, rfl⟩ := hg
  -- expand the monomial in the `y` variables
  have hne : (ζ - 1) ≠ 0 := sub_ne_zero_of_ne hζ1
  have hpt : ∀ x : Fin n → Bool, ((ζ - 1) ^ S.card * mon F S x)
      = ∑ T ∈ S.powerset, (-1 : F) ^ (S.card - T.card) * yMon ζ T x := by
    intro x
    have h0 : ((ζ - 1) ^ S.card * mon F S x) = ∏ i ∈ S, ((1 + (ζ - 1) * bv F (x i)) + (-1)) := by
      rw [mon]
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by ring
    rw [h0, Finset.prod_add]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    rw [Finset.prod_const, Finset.card_sdiff_of_subset hT]
    rw [yMon]
    ring
  have hfun : ((ζ - 1) ^ S.card) • mon F S
      = ∑ T ∈ S.powerset, ((-1 : F) ^ (S.card - T.card)) • yMon ζ T := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    exact hpt x
  have hmem : ((ζ - 1) ^ S.card) • mon F S ∈ Submodule.span F (Set.range (yMon ζ (n := n))) := by
    rw [hfun]
    exact Submodule.sum_mem _ fun T _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)
  have : mon F S = ((ζ - 1) ^ S.card)⁻¹ • (((ζ - 1) ^ S.card) • mon F S) := by
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hne), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ hmem

/-- **The key step of Smolensky's lower bound.**  If `x ↦ ζ^{|x|}` agrees on `G` with a
function of degree `D`, then every function on `G` agrees with a function of degree
`n/2 + D`, so `G` has at most `∑_{i ≤ n/2 + D} C(n,i)` elements. -/
theorem card_le_of_approx {D : ℕ} (ζ : F) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (G : Finset (Fin n → Bool)) (Q : (Fin n → Bool) → F) (hQ : Q ∈ LD F n D)
    (hQG : ∀ x ∈ G, Q x = ζ ^ (count x)) :
    G.card ≤ ∑ i ∈ Finset.range (n / 2 + D + 1), n.choose i := by
  -- every `y`-monomial agrees on `G` with a function of low degree
  have key : ∀ S : Finset (Fin n), ∃ w ∈ LD F n (n / 2 + D), ∀ x ∈ G, yMon ζ S x = w x := by
    intro S
    by_cases hS : S.card ≤ n / 2
    · exact ⟨yMon ζ S, LD_mono (by omega) (yMon_mem_LD ζ S), fun x _ => rfl⟩
    · refine ⟨Q * yMon ζ⁻¹ Sᶜ, ?_, ?_⟩
      · have h1 := mul_mem_LD hQ (yMon_mem_LD (ζ⁻¹) Sᶜ)
        refine LD_mono ?_ h1
        have : Sᶜ.card = n - S.card := by
          rw [Finset.card_compl]
          simp
        have hSn : S.card ≤ n := by
          simpa using Finset.card_le_card (Finset.subset_univ S)
        omega
      · intro x hx
        have hc : (S.filter (fun i => x i = true)).card + (Sᶜ.filter (fun i => x i = true)).card
            = count x := by
          rw [count]
          rw [← Finset.card_union_of_disjoint]
          · congr 1
            ext i
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl, Finset.mem_univ,
              true_and]
            tauto
          · refine Finset.disjoint_left.2 fun i hi hi' => ?_
            simp only [Finset.mem_filter, Finset.mem_compl] at hi hi'
            exact hi'.1 hi.1
        simp only [Pi.mul_apply, hQG x hx, yMon_apply]
        rw [← hc, pow_add, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hζ0), mul_one]
  choose w hw hwG using key
  -- the restriction map to `G`
  set R : ((Fin n → Bool) → F) →ₗ[F] ({x // x ∈ G} → F) :=
    LinearMap.funLeft F F (fun (i : {x // x ∈ G}) => (i : Fin n → Bool)) with hR
  have hRsurj : Function.Surjective R :=
    LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective
  have hmap : Submodule.map R (LD F n (n / 2 + D)) = ⊤ := by
    rw [eq_top_iff]
    have h1 : (⊤ : Submodule F ({x // x ∈ G} → F))
        = Submodule.map R (Submodule.span F (Set.range (yMon ζ (n := n)))) := by
      rw [yMon_span hζ1, Submodule.map_top, LinearMap.range_eq_top.2 hRsurj]
    rw [h1, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro g ⟨-, ⟨S, rfl⟩, rfl⟩
    refine ⟨w S, hw S, ?_⟩
    funext i
    exact (hwG S i.1 i.2).symm
  -- dimension count
  have h2 : Module.finrank F ({x // x ∈ G} → F) ≤ Module.finrank F (LD F n (n / 2 + D)) := by
    have := Submodule.finrank_map_le R (LD F n (n / 2 + D))
    rw [hmap] at this
    simpa using this
  have h3 : Module.finrank F ({x // x ∈ G} → F) = G.card := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [h3] at h2
  exact h2.trans (finrank_LD_le _)

end CS

import Mathlib

/-!
# Binomial estimates

Elementary counting estimates used in the Razborov–Smolensky argument:
a bound on the central binomial coefficient, a bound on the number of
subsets of `Fin (2m)` of size at most `m + D`, and the fact that
exponentials beat polynomials.
-/

namespace CS

open Finset

/-- The central binomial coefficient satisfies `(3m+1) * C(2m,m)^2 ≤ 16^m`
(a sharp form of `C(2m,m) ≤ 4^m / √(3m+1)`). -/
theorem central_binom_sq_le (m : ℕ) : (3 * m + 1) * ((2 * m).choose m) ^ 2 ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hrec : (m + 1) * ((2 * (m + 1)).choose (m + 1)) = 2 * (2 * m + 1) * ((2 * m).choose m) :=
        Nat.succ_mul_centralBinom_succ m
      set c := (2 * m).choose m with hc
      set c' := (2 * (m + 1)).choose (m + 1) with hc'
      -- multiply the goal by `(m+1)^2`
      have key : (m + 1) ^ 2 * ((3 * (m + 1) + 1) * c' ^ 2)
          ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
        have h1 : (m + 1) ^ 2 * ((3 * (m + 1) + 1) * c' ^ 2)
            = (3 * m + 4) * ((m + 1) * c') ^ 2 := by ring
        rw [h1, hrec]
        have h2 : (3 * m + 4) * (2 * (2 * m + 1) * c) ^ 2
            = ((2 * m + 1) ^ 2 * (3 * m + 4)) * (4 * c ^ 2) := by ring
        rw [h2]
        have h3 : (2 * m + 1) ^ 2 * (3 * m + 4) ≤ 4 * (m + 1) ^ 2 * (3 * m + 1) := by nlinarith
        calc ((2 * m + 1) ^ 2 * (3 * m + 4)) * (4 * c ^ 2)
            ≤ (4 * (m + 1) ^ 2 * (3 * m + 1)) * (4 * c ^ 2) :=
              Nat.mul_le_mul_right _ h3
          _ = 16 * (m + 1) ^ 2 * ((3 * m + 1) * c ^ 2) := by ring
          _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
          _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
      exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- Exactly half of the binomial mass lies off the middle coefficient. -/
theorem sum_choose_halves (m : ℕ) :
    2 * ∑ i ∈ Finset.range m, (2 * m).choose i + (2 * m).choose m = 2 ^ (2 * m) := by
  have h1 : ∑ i ∈ Finset.range (2 * m + 1), (2 * m).choose i = 2 ^ (2 * m) :=
    Nat.sum_range_choose (2 * m)
  have hsplit : ∑ i ∈ Finset.range (m + 1), (2 * m).choose i
      + ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), (2 * m).choose i
      = ∑ i ∈ Finset.range (2 * m + 1), (2 * m).choose i :=
    Finset.sum_range_add_sum_Ico _ (by omega)
  have hIco : ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), (2 * m).choose i
      = ∑ i ∈ Finset.range m, (2 * m).choose i := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hm : 2 * m + 1 - (m + 1) = m := by omega
    rw [hm]
    rw [← Finset.sum_range_reflect (fun i => (2 * m).choose (m + 1 + i)) m]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have he : m + 1 + (m - 1 - i) = 2 * m - i := by omega
    rw [he, Nat.choose_symm (by omega)]
  rw [hIco, Finset.sum_range_succ] at hsplit
  omega

/-- The number of subsets of `Fin (2m)` of size at most `m + D`. -/
theorem sum_choose_band (m D : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range (m + D + 1), (2 * m).choose i
      ≤ 2 ^ (2 * m - 1) + (D + 1) * ((2 * m).choose m) := by
  have hsplit : ∑ i ∈ Finset.range m, (2 * m).choose i
      + ∑ i ∈ Finset.Ico m (m + D + 1), (2 * m).choose i
      = ∑ i ∈ Finset.range (m + D + 1), (2 * m).choose i :=
    Finset.sum_range_add_sum_Ico _ (by omega)
  have hlow : ∑ i ∈ Finset.range m, (2 * m).choose i ≤ 2 ^ (2 * m - 1) := by
    have h := sum_choose_halves m
    have hpow : 2 ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hhigh : ∑ i ∈ Finset.Ico m (m + D + 1), (2 * m).choose i
      ≤ (D + 1) * ((2 * m).choose m) := by
    have hbnd : ∀ i ∈ Finset.Ico m (m + D + 1), (2 * m).choose i ≤ (2 * m).choose m := by
      intro i _
      have := Nat.choose_le_middle i (2 * m)
      simpa [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using this
    have := Finset.sum_le_card_nsmul _ _ _ hbnd
    simpa [Nat.card_Ico, smul_eq_mul, mul_comm, show m + D + 1 - m = D + 1 from by omega] using this
  omega

/-- Exponentials beat polynomials. -/
theorem exists_pow_gt (A B : ℕ) : ∃ ℓ : ℕ, 1 ≤ ℓ ∧ A * (ℓ + 1) ^ B < 2 ^ ℓ := by
  have hlo : (fun n : ℕ => ((n : ℝ)) ^ B) =o[Filter.atTop] (fun n : ℕ => (2 : ℝ) ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt B (by norm_num)
  have hC : (0:ℝ) < (A : ℝ) * 2 ^ B + 1 := by positivity
  have hev := (hlo.def' (by positivity : (0:ℝ) < 1 / ((A : ℝ) * 2 ^ B + 1))).bound
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  set ℓ := max N 1 with hℓ
  have h1 : N ≤ ℓ := le_max_left _ _
  have h2 : 1 ≤ ℓ := le_max_right _ _
  have hmain := hN ℓ h1
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((ℓ:ℝ)) ^ B),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ) ^ ℓ)] at hmain
  -- convert to naturals
  have hcast : ((A * (ℓ + 1) ^ B : ℕ) : ℝ) < ((2 ^ ℓ : ℕ) : ℝ) := by
    push_cast
    have hle : ((ℓ : ℝ) + 1) ^ B ≤ 2 ^ B * (ℓ : ℝ) ^ B := by
      rw [← mul_pow]
      have h1l : (1:ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h2
      refine pow_le_pow_left₀ (by positivity) (by linarith) B
    calc (A : ℝ) * ((ℓ : ℝ) + 1) ^ B ≤ (A : ℝ) * (2 ^ B * (ℓ : ℝ) ^ B) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((A : ℝ) * 2 ^ B) * (ℓ : ℝ) ^ B := by ring
      _ ≤ ((A : ℝ) * 2 ^ B) * (1 / ((A : ℝ) * 2 ^ B + 1) * (2:ℝ) ^ ℓ) := by
          exact mul_le_mul_of_nonneg_left hmain (by positivity)
      _ < (2:ℝ) ^ ℓ := by
          have hp : (0:ℝ) < (2:ℝ) ^ ℓ := by positivity
          have hKpos : (0:ℝ) < (A : ℝ) * 2 ^ B + 1 := hC
          rw [show ((A : ℝ) * 2 ^ B) * (1 / ((A : ℝ) * 2 ^ B + 1) * (2:ℝ) ^ ℓ)
              = (((A : ℝ) * 2 ^ B) / ((A : ℝ) * 2 ^ B + 1)) * (2:ℝ) ^ ℓ by ring]
          have hlt : ((A : ℝ) * 2 ^ B) / ((A : ℝ) * 2 ^ B + 1) < 1 := by
            rw [div_lt_one hKpos]; linarith
          nlinarith
  exact_mod_cast hcast

end CS

import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# Razborov–Smolensky approximation

Every `AC⁰[q]` circuit of depth `d` and size `s` is approximated, on all but a
`s · 2⁻ˡ` fraction of the inputs, by a function of degree at most `(ℓ (q-1))^d`
over a field of characteristic `q`.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-! ### Elementary facts -/

lemma sum_bv {k : ℕ} (S : Finset (Fin k)) (bl : Fin k → Bool) :
    ∑ i ∈ S, bv F (bl i) = (((S.filter (fun i => bl i = true)).card : ℕ) : F) := by
  simp only [bv]
  rw [Finset.sum_boole]

lemma natCast_pow_char {q : ℕ} (hq : q.Prime) [CharP F q] (m : ℕ) :
    ((m : F)) ^ (q - 1) = if q ∣ m then 0 else 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcast : (m : F) = (ZMod.castHom (dvd_refl q) F) (m : ZMod q) := by simp
  rw [hcast, ← map_pow]
  by_cases h : q ∣ m
  · rw [if_pos h, (ZMod.natCast_eq_zero_iff m q).2 h,
      zero_pow (by have := hq.two_le; omega), map_zero]
  · rw [if_neg h, ZMod.pow_card_sub_one_eq_one
      (fun hc => h ((ZMod.natCast_eq_zero_iff m q).1 hc)), map_one]

/-- At most half of the subsets `S` of a set of indices satisfy `q ∣ #(S ∩ ones)`,
provided there is at least one index with `bl i = true`. -/
theorem card_subsets_dvd_le {k q : ℕ} (hq : 2 ≤ q) (b : Fin k → Bool) (i0 : Fin k)
    (hi0 : b i0 = true) :
    2 * ((univ : Finset (Finset (Fin k))).filter
      (fun S => q ∣ ((S.filter fun i => b i = true).card))).card ≤ 2 ^ k := by
  classical
  set A := (univ : Finset (Finset (Fin k))).filter
      (fun S => q ∣ ((S.filter fun i => b i = true).card)) with hA
  set psi : Finset (Fin k) → Finset (Fin k) := fun S => if i0 ∈ S then S.erase i0 else insert i0 S
    with hpsi
  have hinv : Function.Involutive psi := by
    intro S
    by_cases h : i0 ∈ S
    · simp [hpsi, h, Finset.insert_erase h]
    · simp [hpsi, h, Finset.erase_insert h]
  have hcount : ∀ S : Finset (Fin k), i0 ∈ S →
      ((S.erase i0).filter fun i => b i = true).card + 1
        = (S.filter fun i => b i = true).card := by
    intro S hS
    have h1 : ((S.erase i0).filter fun i => b i = true)
        = (S.filter fun i => b i = true).erase i0 := by
      ext j; simp [Finset.mem_erase, Finset.mem_filter]; tauto
    rw [h1, Finset.card_erase_of_mem (by simp [Finset.mem_filter, hS, hi0])]
    have : 1 ≤ (S.filter fun i => b i = true).card :=
      Finset.card_pos.2 ⟨i0, by simp [Finset.mem_filter, hS, hi0]⟩
    omega
  have hcount2 : ∀ S : Finset (Fin k), i0 ∉ S →
      ((insert i0 S).filter fun i => b i = true).card
        = (S.filter fun i => b i = true).card + 1 := by
    intro S hS
    have h1 : ((insert i0 S).filter fun i => b i = true)
        = insert i0 (S.filter fun i => b i = true) := by
      ext j
      by_cases hj : j = i0 <;> simp [Finset.mem_insert, Finset.mem_filter, hj, hi0]
    rw [h1, Finset.card_insert_of_notMem (by simp [Finset.mem_filter, hS])]
  have hdisj : Disjoint A (A.image psi) := by
    rw [Finset.disjoint_right]
    intro S hS hSA
    simp only [Finset.mem_image] at hS
    obtain ⟨T, hT, rfl⟩ := hS
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hT hSA
    by_cases h : i0 ∈ T
    · simp only [hpsi, h, if_true] at hSA
      rw [← hcount T h] at hT
      have := Nat.le_of_dvd one_pos ((Nat.dvd_add_right hSA).mp hT)
      omega
    · simp only [hpsi, h, if_false] at hSA
      rw [hcount2 T h] at hSA
      have := Nat.le_of_dvd one_pos ((Nat.dvd_add_right hT).mp hSA)
      omega
  have hcard : (A.image psi).card = A.card := Finset.card_image_of_injective _ hinv.injective
  have h2 : A.card + (A.image psi).card ≤ (univ : Finset (Finset (Fin k))).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.subset_univ _)
  rw [hcard] at h2
  simpa [Finset.card_univ, Fintype.card_finset, two_mul] using h2

/-! ### The approximation of an OR gate -/

/-- The Razborov–Smolensky approximation of an unbounded fan-in `OR` gate,
determined by a choice of `ℓ` subsets of the inputs. -/
noncomputable def orApprox (q : ℕ) {k ℓ : ℕ} (g : Fin k → (Fin n → Bool) → F)
    (s : Fin ℓ → Finset (Fin k)) : (Fin n → Bool) → F :=
  1 - ∏ j : Fin ℓ, (1 - (∑ i ∈ s j, g i) ^ (q - 1))

lemma orApprox_apply (q : ℕ) {k ℓ : ℕ} (g : Fin k → (Fin n → Bool) → F)
    (s : Fin ℓ → Finset (Fin k)) (x : Fin n → Bool) :
    orApprox q g s x = 1 - ∏ j : Fin ℓ, (1 - (∑ i ∈ s j, g i x) ^ (q - 1)) := by
  simp [orApprox, Finset.prod_apply, Finset.sum_apply]

lemma orApprox_mem {k ℓ q D : ℕ} (g : Fin k → (Fin n → Bool) → F)
    (hg : ∀ i, g i ∈ LD F n D) (s : Fin ℓ → Finset (Fin k)) :
    orApprox q g s ∈ LD F n (ℓ * ((q - 1) * D)) := by
  refine Submodule.sub_mem _ (one_mem_LD _) ?_
  have hfac : ∀ j : Fin ℓ, (1 - (∑ i ∈ s j, g i) ^ (q - 1) : (Fin n → Bool) → F)
      ∈ LD F n ((q - 1) * D) :=
    fun j => Submodule.sub_mem _ (one_mem_LD _)
      (pow_mem_LD (Submodule.sum_mem _ (fun i _ => hg i)))
  have := prod_mem_LD (Finset.univ : Finset (Fin ℓ))
    (fun j => (1 - (∑ i ∈ s j, g i) ^ (q - 1) : (Fin n → Bool) → F))
    (fun _ => (q - 1) * D) (fun j _ => hfac j)
  simpa using this

lemma orApprox_correct {k ℓ q : ℕ} (hq : q.Prime) [CharP F q]
    (g : Fin k → (Fin n → Bool) → F) (s : Fin ℓ → Finset (Fin k)) (x : Fin n → Bool)
    (bl : Fin k → Bool) (hx : ∀ i, g i x = bv F (bl i))
    (hs : ∀ i0, bl i0 = true → ∃ j, ¬ (q ∣ ((s j).filter (fun i => bl i = true)).card)) :
    orApprox q g s x = bv F (decide (∃ i, bl i = true)) := by
  have hq2 := hq.two_le
  rw [orApprox_apply]
  have hsum : ∀ j : Fin ℓ, (∑ i ∈ s j, g i x)
      = ((((s j).filter (fun i => bl i = true)).card : ℕ) : F) := by
    intro j
    rw [← sum_bv (F := F)]
    exact Finset.sum_congr rfl fun i _ => hx i
  by_cases hex : ∃ i, bl i = true
  · obtain ⟨i0, hi0⟩ := hex
    obtain ⟨j, hj⟩ := hs i0 hi0
    have : ∏ j : Fin ℓ, (1 - (∑ i ∈ s j, g i x) ^ (q - 1)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [hsum j, natCast_pow_char hq, if_neg hj, sub_self]
    rw [this]
    have hex' : ∃ i, bl i = true := ⟨i0, hi0⟩
    simp [bv, hex']
  · push_neg at hex
    have hall : ∀ j : Fin ℓ, ((s j).filter (fun i => bl i = true)) = ∅ := by
      intro j
      refine Finset.filter_eq_empty_iff.2 fun i _ => ?_
      simp [hex i]
    have : ∏ j : Fin ℓ, (1 - (∑ i ∈ s j, g i x) ^ (q - 1)) = 1 := by
      refine Finset.prod_eq_one fun j _ => ?_
      rw [hsum j, hall j]
      simp only [Finset.card_empty, Nat.cast_zero]
      rw [zero_pow (by omega)]
      ring
    rw [this]
    have : ¬ ∃ i, bl i = true := by push_neg; exact hex
    simp [bv, this]

/-! ### The averaging (union bound) step for an OR gate -/

theorem or_gate {q ℓ k D : ℕ} (hq : q.Prime) [CharP F q]
    (g : Fin k → (Fin n → Bool) → F) (hg : ∀ i, g i ∈ LD F n D)
    (bl : Fin k → (Fin n → Bool) → Bool) (E : Finset (Fin n → Bool))
    (hE : ∀ x ∉ E, ∀ i, g i x = bv F (bl i x)) :
    ∃ f ∈ LD F n (ℓ * ((q - 1) * D)),
      2 ^ ℓ * ((univ : Finset (Fin n → Bool)).filter
          (fun x => f x ≠ bv F (decide (∃ i, bl i x = true)))).card
        ≤ 2 ^ ℓ * E.card + 2 ^ n := by
  classical
  have hq2 := hq.two_le
  set Ch : Finset (Fin ℓ → Finset (Fin k)) := univ with hCh
  have hChcard : Ch.card = (2 ^ k) ^ ℓ := by
    simp [hCh, Finset.card_univ, Fintype.card_finset]
  -- the set of inputs where the choice `s` fails, among inputs where all children are correct
  set W : (Fin ℓ → Finset (Fin k)) → Finset (Fin n → Bool) := fun s =>
    (univ : Finset (Fin n → Bool)).filter (fun x => (∃ i, bl i x = true) ∧
      ∀ j, q ∣ (((s j).filter (fun i => bl i x = true)).card)) with hW
  set Bad : (Fin ℓ → Finset (Fin k)) → Finset (Fin n → Bool) := fun s =>
    (univ : Finset (Fin n → Bool)).filter
      (fun x => orApprox q g s x ≠ bv F (decide (∃ i, bl i x = true))) with hBad
  have hsub : ∀ s, Bad s ⊆ E ∪ W s := by
    intro s x hx
    simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_contra hcon
    simp only [Finset.mem_union, not_or] at hcon
    obtain ⟨hxE, hxW⟩ := hcon
    refine hx ?_
    refine orApprox_correct hq g s x (fun i => bl i x) (hE x hxE) ?_
    intro i0 hi0
    by_contra hj
    push_neg at hj
    refine hxW ?_
    simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨i0, hi0⟩, hj⟩
  -- pointwise bound on the number of bad choices
  have hpoint : ∀ x : Fin n → Bool,
      2 ^ ℓ * (Ch.filter (fun s => x ∈ W s)).card ≤ Ch.card := by
    intro x
    by_cases hex : ∃ i, bl i x = true
    · obtain ⟨i0, hi0⟩ := hex
      set A : Finset (Finset (Fin k)) := (univ : Finset (Finset (Fin k))).filter
        (fun S => q ∣ ((S.filter fun i => bl i x = true).card)) with hAdef
      have hsubA : (Ch.filter (fun s => x ∈ W s)) ⊆ Fintype.piFinset (fun _ : Fin ℓ => A) := by
        intro s hs
        simp only [Finset.mem_filter, hW, Finset.mem_univ, true_and] at hs
        exact Fintype.mem_piFinset.2 fun j => by
          simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hs.2.2 j
      have hcardA : (Fintype.piFinset (fun _ : Fin ℓ => A)).card = A.card ^ ℓ := by
        rw [Fintype.card_piFinset]; simp
      have h2A : 2 * A.card ≤ 2 ^ k := card_subsets_dvd_le hq2 (fun i => bl i x) i0 hi0
      calc 2 ^ ℓ * (Ch.filter (fun s => x ∈ W s)).card
          ≤ 2 ^ ℓ * A.card ^ ℓ := by
            exact Nat.mul_le_mul_left _ (by
              rw [← hcardA]; exact Finset.card_le_card hsubA)
        _ = (2 * A.card) ^ ℓ := by rw [mul_pow]
        _ ≤ (2 ^ k) ^ ℓ := Nat.pow_le_pow_left h2A ℓ
        _ = Ch.card := hChcard.symm
    · have : (Ch.filter (fun s => x ∈ W s)) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun s _ => ?_
        simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h
        exact absurd h hex
      simp [this]
  -- sum over all choices
  have hswap : ∑ s ∈ Ch, (W s).card = ∑ x : Fin n → Bool, (Ch.filter (fun s => x ∈ W s)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.card_eq_sum_ones]
    simp only [hW, Finset.sum_filter]
    exact Finset.sum_congr rfl fun x _ => by
      by_cases h : (∃ i, bl i x = true) ∧ ∀ j, q ∣ (((s j).filter (fun i => bl i x = true)).card)
        <;> simp [h]
  have hsum : 2 ^ ℓ * ∑ s ∈ Ch, (W s).card ≤ 2 ^ n * Ch.card := by
    rw [hswap, Finset.mul_sum]
    calc ∑ x : Fin n → Bool, 2 ^ ℓ * (Ch.filter (fun s => x ∈ W s)).card
        ≤ ∑ _x : Fin n → Bool, Ch.card := Finset.sum_le_sum fun x _ => hpoint x
      _ = 2 ^ n * Ch.card := by
          simp [Finset.card_univ]
  have htotal : ∑ s ∈ Ch, (2 ^ ℓ * (Bad s).card) ≤ ∑ _s ∈ Ch, (2 ^ ℓ * E.card + 2 ^ n) := by
    have h1 : ∑ s ∈ Ch, (2 ^ ℓ * (Bad s).card) ≤ ∑ s ∈ Ch, (2 ^ ℓ * (E.card + (W s).card)) := by
      refine Finset.sum_le_sum fun s _ => Nat.mul_le_mul_left _ ?_
      exact (Finset.card_le_card (hsub s)).trans (Finset.card_union_le _ _)
    refine h1.trans ?_
    have h2 : ∑ s ∈ Ch, (2 ^ ℓ * (E.card + (W s).card))
        = Ch.card * (2 ^ ℓ * E.card) + 2 ^ ℓ * ∑ s ∈ Ch, (W s).card := by
      simp [Finset.mul_sum, Nat.mul_add, Finset.sum_add_distrib, mul_comm]
    rw [h2, Finset.sum_const, smul_eq_mul, Nat.mul_add]
    exact Nat.add_le_add_left (hsum.trans (by rw [mul_comm])) _
  have hne : Ch.Nonempty := ⟨fun _ => ∅, Finset.mem_univ _⟩
  obtain ⟨s, -, hs⟩ := Finset.exists_le_of_sum_le hne htotal
  exact ⟨orApprox q g s, orApprox_mem g hg s, hs⟩

/-- The same for an AND gate, by De Morgan. -/
theorem and_gate {q ℓ k D : ℕ} (hq : q.Prime) [CharP F q]
    (g : Fin k → (Fin n → Bool) → F) (hg : ∀ i, g i ∈ LD F n D)
    (bl : Fin k → (Fin n → Bool) → Bool) (E : Finset (Fin n → Bool))
    (hE : ∀ x ∉ E, ∀ i, g i x = bv F (bl i x)) :
    ∃ f ∈ LD F n (ℓ * ((q - 1) * D)),
      2 ^ ℓ * ((univ : Finset (Fin n → Bool)).filter
          (fun x => f x ≠ bv F (decide (∀ i, bl i x = true)))).card
        ≤ 2 ^ ℓ * E.card + 2 ^ n := by
  classical
  have hg' : ∀ i, (1 - g i : (Fin n → Bool) → F) ∈ LD F n D :=
    fun i => Submodule.sub_mem _ (one_mem_LD _) (hg i)
  have hE' : ∀ x ∉ E, ∀ i, (1 - g i : (Fin n → Bool) → F) x = bv F ((!bl i x)) := by
    intro x hx i
    simp only [Pi.sub_apply, Pi.one_apply, hE x hx i, bv_not]
  obtain ⟨f₀, hf₀mem, hf₀⟩ := or_gate (ℓ := ℓ) hq (fun i => 1 - g i) hg'
    (fun i x => !(bl i x)) E hE'
  refine ⟨1 - f₀, Submodule.sub_mem _ (one_mem_LD _) hf₀mem, ?_⟩
  have hset : ((univ : Finset (Fin n → Bool)).filter
      (fun x => (1 - f₀ : (Fin n → Bool) → F) x ≠ bv F (decide (∀ i, bl i x = true))))
      = ((univ : Finset (Fin n → Bool)).filter
      (fun x => f₀ x ≠ bv F (decide (∃ i, (!bl i x) = true)))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.one_apply]
    have hb : bv F (decide (∀ i, bl i x = true)) = 1 - bv F (decide (∃ i, (!bl i x) = true)) := by
      by_cases h : ∀ i, bl i x = true
      · have h1 : ¬ ∃ i, bl i x = false := by
          push_neg
          intro i
          simp [h i]
        simp [bv, h, h1]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        have h1 : ∃ i, bl i x = false := ⟨i, Bool.eq_false_iff.mpr hi⟩
        have h2 : ¬ ∀ i, bl i x = true := by push_neg; exact ⟨i, hi⟩
        simp [bv, h1, h2]
    rw [hb]
    constructor
    · intro h hc; exact h (by rw [hc])
    · intro h hc; exact h (by linear_combination -hc)
  rw [hset]
  exact hf₀

/-- A `MOD q` gate is computed *exactly* by a function of degree `q - 1`. -/
theorem mod_gate {q k D : ℕ} (hq : q.Prime) [CharP F q]
    (g : Fin k → (Fin n → Bool) → F) (hg : ∀ i, g i ∈ LD F n D)
    (bl : Fin k → (Fin n → Bool) → Bool) (E : Finset (Fin n → Bool))
    (hE : ∀ x ∉ E, ∀ i, g i x = bv F (bl i x)) :
    ((∑ i, g i) ^ (q - 1) : (Fin n → Bool) → F) ∈ LD F n ((q - 1) * D) ∧
      ∀ x ∉ E, ((∑ i, g i) ^ (q - 1) : (Fin n → Bool) → F) x
        = bv F (decide (¬ (q ∣ ((univ.filter (fun i => bl i x = true)).card)))) := by
  refine ⟨pow_mem_LD (Submodule.sum_mem _ fun i _ => hg i), ?_⟩
  intro x hx
  have : ((∑ i, g i) ^ (q - 1) : (Fin n → Bool) → F) x = (∑ i, g i x) ^ (q - 1) := by
    simp [Finset.sum_apply]
  rw [this]
  have hsum : (∑ i, g i x) = (((univ.filter (fun i => bl i x = true)).card : ℕ) : F) := by
    rw [← sum_bv (F := F)]
    exact Finset.sum_congr rfl fun i _ => hE x hx i
  rw [hsum, natCast_pow_char hq]
  by_cases h : q ∣ ((univ.filter (fun i => bl i x = true)).card) <;> simp [bv, h]

/-! ### The approximation theorem for circuits -/

/-- **Razborov–Smolensky approximation.**  Over a field of characteristic `q`, every
circuit of depth `d` and size `s` over the basis `{AND, OR, NOT, MOD q}` agrees with a
function of degree at most `(ℓ (q-1))^d` on all but at most `s · 2^n / 2^ℓ` inputs. -/
theorem approx_circuit {q : ℕ} (hq : q.Prime) [CharP F q] {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (C : Circuit n) :
    ∃ f ∈ LD F n ((ℓ * (q - 1)) ^ C.depth),
      2 ^ ℓ * ((univ : Finset (Fin n → Bool)).filter (fun x => f x ≠ bv F (C.eval q x))).card
        ≤ C.size * 2 ^ n := by
  classical
  have hq2 := hq.two_le
  have hbase : 1 ≤ ℓ * (q - 1) := Nat.one_le_iff_ne_zero.2 (by
    have : 1 ≤ q - 1 := by omega
    positivity)
  induction C with
  | var i =>
      refine ⟨mon F {i}, ?_, ?_⟩
      · simpa [Circuit.depth] using mon_mem_LD (F := F) (S := ({i} : Finset (Fin n))) (by simp)
      · have : ((univ : Finset (Fin n → Bool)).filter
            (fun x => mon F {i} x ≠ bv F ((Circuit.var i).eval q x))) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun x _ => ?_
          simp [mon, Circuit.eval]
        simp [this, Circuit.size]
  | const b =>
      refine ⟨fun _ => bv F b, const_mem_LD _ _, ?_⟩
      have : ((univ : Finset (Fin n → Bool)).filter
          (fun x => (fun _ => bv F b) x ≠ bv F ((Circuit.const b).eval q x))) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun x _ => ?_
        simp [Circuit.eval]
      simp [this, Circuit.size]
  | not c ih =>
      obtain ⟨f, hf, hbad⟩ := ih
      refine ⟨1 - f, Submodule.sub_mem _ (one_mem_LD _) (by simpa [Circuit.depth] using hf), ?_⟩
      have hset : ((univ : Finset (Fin n → Bool)).filter
          (fun x => (1 - f : (Fin n → Bool) → F) x ≠ bv F ((Circuit.not c).eval q x)))
          = ((univ : Finset (Fin n → Bool)).filter (fun x => f x ≠ bv F (c.eval q x))) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.one_apply,
          Circuit.eval, bv_not]
        constructor
        · intro h hc; exact h (by rw [hc])
        · intro h hc; exact h (by linear_combination -hc)
      rw [hset]
      exact hbad.trans (Nat.mul_le_mul_right _ (by simp [Circuit.size]))
  | or k f ih =>
      choose g hg1 hg2 using ih
      set d0 := (univ : Finset (Fin k)).sup (fun i => (f i).depth) with hd0
      have hgD : ∀ i, g i ∈ LD F n ((ℓ * (q - 1)) ^ d0) := fun i =>
        LD_mono (Nat.pow_le_pow_right hbase (Finset.le_sup (Finset.mem_univ i))) (hg1 i)
      set E : Finset (Fin n → Bool) := (univ : Finset (Fin k)).biUnion
        (fun i => (univ : Finset (Fin n → Bool)).filter
          (fun x => g i x ≠ bv F ((f i).eval q x))) with hEdef
      have hE : ∀ x ∉ E, ∀ i, g i x = bv F ((f i).eval q x) := by
        intro x hx i
        by_contra hc
        exact hx (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, by simp [hc]⟩)
      obtain ⟨f', hf'1, hf'2⟩ := or_gate (ℓ := ℓ) hq g hgD (fun i x => (f i).eval q x) E hE
      have hdeg : ℓ * ((q - 1) * (ℓ * (q - 1)) ^ d0) = (ℓ * (q - 1)) ^ (Circuit.or k f).depth := by
        simp only [Circuit.depth, ← hd0]
        rw [pow_add, pow_one, mul_assoc]
      refine ⟨f', by rwa [hdeg] at hf'1, ?_⟩
      have hEcard : 2 ^ ℓ * E.card ≤ (∑ i, (f i).size) * 2 ^ n := by
        calc 2 ^ ℓ * E.card
            ≤ 2 ^ ℓ * ∑ i, ((univ : Finset (Fin n → Bool)).filter
                (fun x => g i x ≠ bv F ((f i).eval q x))).card :=
              Nat.mul_le_mul_left _ (Finset.card_biUnion_le)
          _ = ∑ i, 2 ^ ℓ * ((univ : Finset (Fin n → Bool)).filter
                (fun x => g i x ≠ bv F ((f i).eval q x))).card := by rw [Finset.mul_sum]
          _ ≤ ∑ i, (f i).size * 2 ^ n := Finset.sum_le_sum fun i _ => hg2 i
          _ = (∑ i, (f i).size) * 2 ^ n := by rw [Finset.sum_mul]
      have heval : ∀ x, (Circuit.or k f).eval q x = decide (∃ i, (f i).eval q x = true) := by
        intro x; rfl
      simp only [heval]
      refine hf'2.trans ?_
      rw [Circuit.size, Nat.add_mul, one_mul]
      omega
  | and k f ih =>
      choose g hg1 hg2 using ih
      set d0 := (univ : Finset (Fin k)).sup (fun i => (f i).depth) with hd0
      have hgD : ∀ i, g i ∈ LD F n ((ℓ * (q - 1)) ^ d0) := fun i =>
        LD_mono (Nat.pow_le_pow_right hbase (Finset.le_sup (Finset.mem_univ i))) (hg1 i)
      set E : Finset (Fin n → Bool) := (univ : Finset (Fin k)).biUnion
        (fun i => (univ : Finset (Fin n → Bool)).filter
          (fun x => g i x ≠ bv F ((f i).eval q x))) with hEdef
      have hE : ∀ x ∉ E, ∀ i, g i x = bv F ((f i).eval q x) := by
        intro x hx i
        by_contra hc
        exact hx (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, by simp [hc]⟩)
      obtain ⟨f', hf'1, hf'2⟩ := and_gate (ℓ := ℓ) hq g hgD (fun i x => (f i).eval q x) E hE
      have hdeg : ℓ * ((q - 1) * (ℓ * (q - 1)) ^ d0) = (ℓ * (q - 1)) ^ (Circuit.and k f).depth := by
        simp only [Circuit.depth, ← hd0]
        rw [pow_add, pow_one, mul_assoc]
      refine ⟨f', by rwa [hdeg] at hf'1, ?_⟩
      have hEcard : 2 ^ ℓ * E.card ≤ (∑ i, (f i).size) * 2 ^ n := by
        calc 2 ^ ℓ * E.card
            ≤ 2 ^ ℓ * ∑ i, ((univ : Finset (Fin n → Bool)).filter
                (fun x => g i x ≠ bv F ((f i).eval q x))).card :=
              Nat.mul_le_mul_left _ (Finset.card_biUnion_le)
          _ = ∑ i, 2 ^ ℓ * ((univ : Finset (Fin n → Bool)).filter
                (fun x => g i x ≠ bv F ((f i).eval q x))).card := by rw [Finset.mul_sum]
          _ ≤ ∑ i, (f i).size * 2 ^ n := Finset.sum_le_sum fun i _ => hg2 i
          _ = (∑ i, (f i).size) * 2 ^ n := by rw [Finset.sum_mul]
      have heval : ∀ x, (Circuit.and k f).eval q x = decide (∀ i, (f i).eval q x = true) := by
        intro x; rfl
      simp only [heval]
      refine hf'2.trans ?_
      rw [Circuit.size, Nat.add_mul, one_mul]
      omega
  | mod k f ih =>
      choose g hg1 hg2 using ih
      set d0 := (univ : Finset (Fin k)).sup (fun i => (f i).depth) with hd0
      have hgD : ∀ i, g i ∈ LD F n ((ℓ * (q - 1)) ^ d0) := fun i =>
        LD_mono (Nat.pow_le_pow_right hbase (Finset.le_sup (Finset.mem_univ i))) (hg1 i)
      set E : Finset (Fin n → Bool) := (univ : Finset (Fin k)).biUnion
        (fun i => (univ : Finset (Fin n → Bool)).filter
          (fun x => g i x ≠ bv F ((f i).eval q x))) with hEdef
      have hE : ∀ x ∉ E, ∀ i, g i x = bv F ((f i).eval q x) := by
        intro x hx i
        by_contra hc
        exact hx (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, by simp [hc]⟩)
      obtain ⟨hf'1, hf'2⟩ := mod_gate hq g hgD (fun i x => (f i).eval q x) E hE
      refine ⟨(∑ i, g i) ^ (q - 1), ?_, ?_⟩
      · refine LD_mono ?_ hf'1
        calc (q - 1) * (ℓ * (q - 1)) ^ d0 ≤ (ℓ * (q - 1)) * (ℓ * (q - 1)) ^ d0 :=
              Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega))
          _ = (ℓ * (q - 1)) ^ (Circuit.mod k f).depth := by
              simp only [Circuit.depth, ← hd0]; rw [pow_add, pow_one]
      · have hsub : ((univ : Finset (Fin n → Bool)).filter
            (fun x => ((∑ i, g i) ^ (q - 1) : (Fin n → Bool) → F) x
              ≠ bv F ((Circuit.mod k f).eval q x))) ⊆ E := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          by_contra hxE
          exact hx (hf'2 x hxE)
        have hEcard : 2 ^ ℓ * E.card ≤ (∑ i, (f i).size) * 2 ^ n := by
          calc 2 ^ ℓ * E.card
              ≤ 2 ^ ℓ * ∑ i, ((univ : Finset (Fin n → Bool)).filter
                  (fun x => g i x ≠ bv F ((f i).eval q x))).card :=
                Nat.mul_le_mul_left _ (Finset.card_biUnion_le)
            _ = ∑ i, 2 ^ ℓ * ((univ : Finset (Fin n → Bool)).filter
                  (fun x => g i x ≠ bv F ((f i).eval q x))).card := by rw [Finset.mul_sum]
            _ ≤ ∑ i, (f i).size * 2 ^ n := Finset.sum_le_sum fun i _ => hg2 i
            _ = (∑ i, (f i).size) * 2 ^ n := by rw [Finset.sum_mul]
        have := Nat.mul_le_mul_left (2 ^ ℓ) (Finset.card_le_card hsub)
        refine this.trans (hEcard.trans ?_)
        rw [Circuit.size, Nat.add_mul, one_mul]
        exact Nat.le_add_left _ _

end CS

import Mathlib

/-!
# A field of characteristic `q` containing a primitive `p`-th root of unity

For distinct primes `p ≠ q`, Fermat's little theorem gives `p ∣ q^(p-1) - 1`, so the
field `GF(q^(p-1))` has a `p`-th root of unity different from `1`.
-/

namespace CS

/-- For distinct primes `p ≠ q`, the field `GF(q^(p-1))` contains a primitive `p`-th
root of unity. -/
theorem exists_root_of_unity (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    [Fact q.Prime] :
    ∃ ζ : GaloisField q (p - 1), ζ ^ p = 1 ∧ ζ ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hk : p - 1 ≠ 0 := by omega
  -- Fermat's little theorem: `p ∣ q ^ (p-1) - 1`
  have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp).2 (Ne.symm hpq)
  have hmod : q ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hp] at this
  have hone : 1 ≤ q ^ (p - 1) := Nat.one_le_pow _ _ hq.pos
  have hdvd : p ∣ q ^ (p - 1) - 1 := (Nat.modEq_iff_dvd' hone).1 hmod.symm
  -- the multiplicative group of `GF(q^(p-1))` has order divisible by `p`
  haveI : Fintype (GaloisField q (p - 1)) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField q (p - 1)) = q ^ (p - 1) := GaloisField.card q (p - 1) hk
  have hunits : Fintype.card (GaloisField q (p - 1))ˣ = q ^ (p - 1) - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hcard]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (GaloisField q (p - 1))ˣ) p
    (by rw [hunits]; exact hdvd)
  refine ⟨(u : GaloisField q (p - 1)), ?_, ?_⟩
  · have h1 : u ^ p = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have := congrArg (Units.val) h1
    push_cast at this
    exact this
  · intro h
    have hu1 : u = 1 := Units.ext h
    rw [hu1, orderOf_one] at hu
    omega

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
# Boolean circuits with unbounded fan-in AND / OR / NOT and MOD gates

This file sets up the circuit model used in the Razborov–Smolensky theorem:
constant depth, polynomial size circuits over the basis
`{AND, OR, NOT, MOD_q}` (the class `AC⁰[q]`).
-/

namespace CS

open Finset

/-- Boolean circuits over the basis `{AND, OR, NOT, MOD}` with unbounded fan-in
(`AND`, `OR` and `MOD` gates take an arbitrary finite family of subcircuits). -/
inductive Circuit (n : ℕ) : Type
  | var (i : Fin n)
  | const (b : Bool)
  | not (c : Circuit n)
  | and (k : ℕ) (f : Fin k → Circuit n)
  | or (k : ℕ) (f : Fin k → Circuit n)
  | mod (k : ℕ) (f : Fin k → Circuit n)

namespace Circuit

/-- Semantics of a circuit; the `mod` gate is the `MOD_q` gate, which outputs `true`
iff the number of its inputs that are `true` is *not* divisible by `q`. -/
def eval (q : ℕ) {n : ℕ} : Circuit n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .const b, _ => b
  | .not c, x => !(c.eval q x)
  | .and _ f, x => decide (∀ i, (f i).eval q x = true)
  | .or _ f, x => decide (∃ i, (f i).eval q x = true)
  | .mod _ f, x => decide (¬ (q ∣ (Finset.univ.filter (fun i => (f i).eval q x = true)).card))

/-- The number of gates of a circuit. -/
def size {n : ℕ} : Circuit n → ℕ
  | .var _ => 1
  | .const _ => 1
  | .not c => c.size + 1
  | .and _ f => 1 + ∑ i, (f i).size
  | .or _ f => 1 + ∑ i, (f i).size
  | .mod _ f => 1 + ∑ i, (f i).size

/-- The depth of a circuit, counting only `AND`, `OR` and `MOD` gates
(`NOT` gates are free, as usual). -/
def depth {n : ℕ} : Circuit n → ℕ
  | .var _ => 0
  | .const _ => 0
  | .not c => c.depth
  | .and _ f => 1 + Finset.univ.sup (fun i => (f i).depth)
  | .or _ f => 1 + Finset.univ.sup (fun i => (f i).depth)
  | .mod _ f => 1 + Finset.univ.sup (fun i => (f i).depth)

/-- Substituting variables by variables or constants. -/
def pull {m n : ℕ} (σ : Fin m → Fin n ⊕ Bool) : Circuit m → Circuit n
  | .var i => match σ i with
      | .inl j => .var j
      | .inr b => .const b
  | .const b => .const b
  | .not c => .not (pull σ c)
  | .and k f => .and k (fun i => pull σ (f i))
  | .or k f => .or k (fun i => pull σ (f i))
  | .mod k f => .mod k (fun i => pull σ (f i))

@[simp] lemma size_pull {m n : ℕ} (σ : Fin m → Fin n ⊕ Bool) (C : Circuit m) :
    (pull σ C).size = C.size := by
  induction C with
  | var i => cases h : σ i <;> simp [pull, size, h]
  | const b => simp [pull, size]
  | not c ih => simp [pull, size, ih]
  | and k f ih => simp [pull, size, ih]
  | or k f ih => simp [pull, size, ih]
  | mod k f ih => simp [pull, size, ih]

@[simp] lemma depth_pull {m n : ℕ} (σ : Fin m → Fin n ⊕ Bool) (C : Circuit m) :
    (pull σ C).depth = C.depth := by
  induction C with
  | var i => cases h : σ i <;> simp [pull, depth, h]
  | const b => simp [pull, depth]
  | not c ih => simp [pull, depth, ih]
  | and k f ih => simp [pull, depth, ih]
  | or k f ih => simp [pull, depth, ih]
  | mod k f ih => simp [pull, depth, ih]

@[simp] lemma eval_pull {m n q : ℕ} (σ : Fin m → Fin n ⊕ Bool) (C : Circuit m)
    (x : Fin n → Bool) :
    (pull σ C).eval q x = C.eval q (fun i => Sum.elim x id (σ i)) := by
  induction C with
  | var i => cases h : σ i <;> simp [pull, eval, h]
  | const b => simp [pull, eval]
  | not c ih => simp [pull, eval, ih]
  | and k f ih => simp [pull, eval, ih]
  | or k f ih => simp [pull, eval, ih]
  | mod k f ih => simp [pull, eval, ih]

end Circuit

/-- The number of `true` coordinates of a Boolean input. -/
def count {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

/-- The `MOD_p` function: `true` iff the number of ones is divisible by `p`. -/
def modp (p : ℕ) {n : ℕ} (x : Fin n → Bool) : Bool := decide (p ∣ count x)

/-- `F ∈ AC⁰[q]`: there is a family of circuits over the basis `{AND, OR, NOT, MOD_q}`
of constant depth and polynomial size computing `F`. -/
def AC0mod (q : ℕ) (F : ∀ n, (Fin n → Bool) → Bool) : Prop :=
  ∃ (d c : ℕ) (C : ∀ n, Circuit n),
    (∀ n, (C n).depth ≤ d) ∧ (∀ n, (C n).size ≤ n ^ c + c) ∧
      ∀ n x, (C n).eval q x = F n x

end CS

import Mathlib

/-!
# Low degree functions on the Boolean cube

We work with the `F`-algebra of functions from the Boolean cube `Fin n → Bool` to a
field `F`, and with the subspaces `LD F n D` spanned by the multilinear monomials of
degree at most `D`.  This replaces multivariate polynomials: since we only ever care
about the *values* of polynomials on the cube, working with the spanned function
spaces directly is more convenient.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- A boolean, as an element of `F`. -/
def bv (F : Type*) [Field F] (b : Bool) : F := if b then 1 else 0

@[simp] lemma bv_true : bv F true = 1 := rfl
@[simp] lemma bv_false : bv F false = 0 := rfl

lemma bv_eq_zero_iff {b : Bool} : bv F b = 0 ↔ b = false := by
  cases b <;> simp [bv]

lemma bv_eq_one_iff {b : Bool} : bv F b = 1 ↔ b = true := by
  cases b <;> simp [bv]

lemma bv_not (b : Bool) : bv F (!b) = 1 - bv F b := by cases b <;> simp

/-- The multilinear monomial `∏_{i ∈ S} x_i`, as a function on the cube. -/
def mon (F : Type*) [Field F] {n : ℕ} (S : Finset (Fin n)) : (Fin n → Bool) → F :=
  fun x => ∏ i ∈ S, bv F (x i)

lemma mon_apply (S : Finset (Fin n)) (x : Fin n → Bool) :
    mon F S x = if (∀ i ∈ S, x i = true) then 1 else 0 := by
  unfold mon
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos h]
    exact Finset.prod_eq_one fun i hi => by simp [h i hi]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hix⟩ := h
    exact Finset.prod_eq_zero hi (by simp [bv, Bool.eq_false_iff.mpr hix])

@[simp] lemma mon_empty : mon F (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mon]

lemma mon_mul (S T : Finset (Fin n)) : mon F S * mon F T = mon F (S ∪ T) := by
  funext x
  simp only [Pi.mul_apply, mon_apply]
  by_cases hS : ∀ i ∈ S, x i = true <;> by_cases hT : ∀ i ∈ T, x i = true <;>
    simp_all [Finset.mem_union] <;> aesop

/-- The set of monomials of degree at most `D`. -/
noncomputable def monFinset (F : Type*) [Field F] (n D : ℕ) : Finset ((Fin n → Bool) → F) :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).image (mon F)

/-- The space of functions of degree at most `D` on the cube. -/
noncomputable def LD (F : Type*) [Field F] (n D : ℕ) : Submodule F ((Fin n → Bool) → F) :=
  Submodule.span F (monFinset F n D : Set ((Fin n → Bool) → F))

lemma mon_mem_LD {S : Finset (Fin n)} {D : ℕ} (h : S.card ≤ D) : mon F S ∈ LD F n D := by
  apply Submodule.subset_span
  simp only [monFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
  exact ⟨S, ⟨Finset.mem_univ _, h⟩, rfl⟩

lemma LD_mono {D D' : ℕ} (h : D ≤ D') : LD F n D ≤ LD F n D' := by
  apply Submodule.span_le.2
  intro g hg
  simp only [monFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hg
  obtain ⟨S, ⟨-, hS⟩, rfl⟩ := hg
  exact mon_mem_LD (hS.trans h)

lemma one_mem_LD (D : ℕ) : (1 : (Fin n → Bool) → F) ∈ LD F n D := by
  have := mon_mem_LD (F := F) (S := (∅ : Finset (Fin n))) (D := D) (by simp)
  simpa using this

lemma const_mem_LD (c : F) (D : ℕ) : (fun _ => c : (Fin n → Bool) → F) ∈ LD F n D := by
  have : (fun _ => c : (Fin n → Bool) → F) = c • (1 : (Fin n → Bool) → F) := by
    funext x; simp
  rw [this]
  exact Submodule.smul_mem _ _ (one_mem_LD D)

lemma coord_mem_LD (i : Fin n) (D : ℕ) (hD : 1 ≤ D) :
    (fun x => bv F (x i) : (Fin n → Bool) → F) ∈ LD F n D := by
  have : (fun x => bv F (x i) : (Fin n → Bool) → F) = mon F {i} := by
    funext x; simp [mon]
  rw [this]
  exact mon_mem_LD (by simpa using hD)

lemma mul_mem_LD {D₁ D₂ : ℕ} {f g : (Fin n → Bool) → F}
    (hf : f ∈ LD F n D₁) (hg : g ∈ LD F n D₂) : f * g ∈ LD F n (D₁ + D₂) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      induction hg using Submodule.span_induction with
      | mem g hg =>
          simp only [monFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe,
            Finset.mem_filter] at hf hg
          obtain ⟨S, ⟨-, hS⟩, rfl⟩ := hf
          obtain ⟨T, ⟨-, hT⟩, rfl⟩ := hg
          rw [mon_mul]
          exact mon_mem_LD ((Finset.card_union_le _ _).trans (Nat.add_le_add hS hT))
      | zero => simp
      | add g₁ g₂ _ _ ih₁ ih₂ => rw [mul_add]; exact Submodule.add_mem _ ih₁ ih₂
      | smul a g _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
  | zero => simp
  | add f₁ f₂ _ _ ih₁ ih₂ => rw [add_mul]; exact Submodule.add_mem _ ih₁ ih₂
  | smul a f _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih

lemma prod_mem_LD {ι : Type*} (s : Finset ι) (g : ι → (Fin n → Bool) → F) (d : ι → ℕ)
    (h : ∀ i ∈ s, g i ∈ LD F n (d i)) : (∏ i ∈ s, g i) ∈ LD F n (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_LD 0
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact mul_mem_LD (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

lemma pow_mem_LD {D k : ℕ} {f : (Fin n → Bool) → F} (hf : f ∈ LD F n D) :
    f ^ k ∈ LD F n (k * D) := by
  induction k with
  | zero => simpa using one_mem_LD 0
  | succ k ih =>
      have : f ^ (k + 1) = f ^ k * f := by ring
      rw [this]
      have := mul_mem_LD ih hf
      exact (LD_mono (by ring_nf; omega)) this

lemma sum_mem_LD {ι : Type*} (s : Finset ι) (g : ι → (Fin n → Bool) → F) (D : ℕ)
    (h : ∀ i ∈ s, g i ∈ LD F n D) : (∑ i ∈ s, g i) ∈ LD F n D :=
  Submodule.sum_mem _ h

/-- The indicator function of a point of the cube. -/
noncomputable def delta (F : Type*) [Field F] {n : ℕ} (a : Fin n → Bool) :
    (Fin n → Bool) → F :=
  fun x => if x = a then 1 else 0

lemma delta_mem_LD (a : Fin n → Bool) : delta F a ∈ LD F n n := by
  have key : delta F a
      = ∏ i : Fin n, (fun x : Fin n → Bool =>
          if a i then bv F (x i) else 1 - bv F (x i) : (Fin n → Bool) → F) := by
    funext x
    simp only [Finset.prod_apply, delta]
    by_cases hx : x = a
    · subst hx
      rw [if_pos rfl]
      refine (Finset.prod_eq_one fun i _ => ?_).symm
      cases h : x i <;> simp [h]
    · rw [if_neg hx]
      have : ∃ i, x i ≠ a i := by
        by_contra h
        push_neg at h
        exact hx (funext h)
      obtain ⟨i, hi⟩ := this
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      cases ha : a i <;> cases hxi : x i <;> simp_all
  rw [key]
  have h2 : (∏ i : Fin n, (fun x : Fin n → Bool =>
      if a i then bv F (x i) else 1 - bv F (x i) : (Fin n → Bool) → F))
      ∈ LD F n (∑ _i : Fin n, (1 : ℕ)) := by
    refine prod_mem_LD _ _ _ fun i _ => ?_
    by_cases h : a i
    · simp only [h, if_true]
      exact coord_mem_LD i 1 le_rfl
    · simp only [h, if_false, Bool.false_eq_true]
      exact Submodule.sub_mem _ (one_mem_LD 1) (coord_mem_LD i 1 le_rfl)
  simpa using h2

/-- Every function on the cube has degree at most `n`. -/
lemma LD_top : LD F n n = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have : f = ∑ a : Fin n → Bool, f a • delta F a := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, delta, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single x] <;> simp +contextual [eq_comm]
  rw [this]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (delta_mem_LD a)

/-- The dimension of the space of functions of degree at most `D` is bounded by the
number of monomials of degree at most `D`. -/
lemma finrank_LD_le (D : ℕ) :
    Module.finrank F (LD F n D) ≤ ∑ i ∈ Finset.range (D + 1), n.choose i := by
  have h1 : Module.finrank F (LD F n D) ≤ (monFinset F n D).card :=
    finrank_span_finset_le_card _
  refine h1.trans ?_
  refine (Finset.card_image_le).trans ?_
  have : ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).card
      = ∑ i ∈ Finset.range (D + 1), n.choose i := by
    have : ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D))
        = (Finset.range (D + 1)).biUnion
            (fun i => Finset.powersetCard i (Finset.univ : Finset (Fin n))) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      constructor
      · intro h; exact ⟨S.card, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩; omega
    rw [this, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.card_powersetCard]
      simp
    · intro i _ j _ hij
      simp only [Finset.disjoint_left, Finset.mem_powersetCard]
      rintro S ⟨-, rfl⟩ ⟨-, h⟩
      exact hij h
  exact this.le

end CS

