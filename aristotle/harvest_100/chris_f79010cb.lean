/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The cap-set bound: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have size
`o(3ⁿ)`.  This is the Croot–Lev–Pach / Ellenberg–Gijswijt theorem, proved here by the
polynomial method.
-/

open Finset

namespace Math2
namespace CapSet

instance factThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The field `𝔽₃`. -/
abbrev F := ZMod 3

/-- The vector space `𝔽₃ⁿ`. -/
abbrev V (n : ℕ) := Fin n → F

/-- Exponent vectors of reduced monomials: each exponent is `0`, `1` or `2`. -/
abbrev E (n : ℕ) := Fin n → Fin 3

/-- Total degree of a reduced monomial. -/
def deg {n : ℕ} (a : E n) : ℕ := ∑ i, (a i : ℕ)

/-- The monomial function `x ↦ ∏ xᵢ ^ aᵢ`. -/
def mon {n : ℕ} (a : E n) : V n → F := fun x => ∏ i, (x i) ^ (a i : ℕ)

/-- Exponent vectors of degree at most `d`. -/
def M (n d : ℕ) : Finset (E n) := Finset.univ.filter (fun a => deg a ≤ d)

/-- The space of functions spanned by monomials of degree at most `d`. -/
def W (n d : ℕ) : Submodule F (V n → F) := Submodule.span F (mon '' (M n d : Set (E n)))

section Basic

lemma sq_ne : ∀ u : F, u ≠ 0 → u ^ 2 = 1 := by decide

lemma quad_expand : ∀ v u : F, 1 - (u - v) ^ 2 = ∑ j : Fin 3,
    (if (j : ℕ) = 0 then 1 - v ^ 2 else if (j : ℕ) = 1 then 2 * v else -1) * u ^ (j : ℕ) := by
  decide

lemma binom_expand : ∀ (k : Fin 3) (u v : F), (u + v) ^ (k : ℕ) =
    ∑ j : Fin 3, (((k : ℕ).choose (j : ℕ) : ℕ) : F) * (u ^ (j : ℕ) * v ^ ((k : ℕ) - (j : ℕ))) := by
  decide

lemma delta_prod {n : ℕ} (c x : V n) :
    (∏ i, (1 - (x i - c i) ^ 2)) = if x = c then 1 else 0 := by
  by_cases h : x = c
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ c i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [sq_ne _ (sub_ne_zero.mpr hi)]; ring

lemma delta_mem_span {n : ℕ} (c : V n) :
    (fun x => if x = c then (1 : F) else 0) ∈ Submodule.span F (Set.range (mon (n := n))) := by
  have key : (fun x : V n => if x = c then (1 : F) else 0)
      = ∑ a : E n, (∏ i, (if (a i : ℕ) = 0 then 1 - (c i) ^ 2
          else if (a i : ℕ) = 1 then 2 * (c i) else -1)) • mon a := by
    funext x
    rw [← delta_prod c x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mon]
    have h1 : ∀ i : Fin n, (1 - (x i - c i) ^ 2) = ∑ j : Fin 3,
        (if (j : ℕ) = 0 then 1 - (c i) ^ 2 else if (j : ℕ) = 1 then 2 * (c i) else -1)
          * (x i) ^ (j : ℕ) := fun i => quad_expand (c i) (x i)
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun a _ => Finset.prod_mul_distrib)
  rw [key]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

lemma mon_span_top {n : ℕ} :
    (⊤ : Submodule F (V n → F)) ≤ Submodule.span F (Set.range (mon (n := n))) := by
  rintro f -
  have : f = ∑ c : V n, f c • (fun x => if x = c then (1 : F) else 0) := by
    funext x; simp [Finset.sum_apply, Finset.sum_ite_eq]
  rw [this]
  exact Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (delta_mem_span c))

lemma card_E_eq {n : ℕ} : Fintype.card (E n) = Module.finrank F (V n → F) := by
  rw [Module.finrank_fintype_fun_eq_card]; simp [E, V]

/-- The monomials form a basis of the space of all functions `𝔽₃ⁿ → 𝔽₃`. -/
noncomputable def monBasis (n : ℕ) : Module.Basis (E n) F (V n → F) :=
  basisOfTopLeSpanOfCardEqFinrank _ mon_span_top card_E_eq

lemma mon_linearIndependent {n : ℕ} : LinearIndependent F (mon (n := n)) := by
  have h := (monBasis n).linearIndependent
  rwa [monBasis, coe_basisOfTopLeSpanOfCardEqFinrank] at h

lemma card_M_le_finrank_W (n d : ℕ) : (M n d).card ≤ Module.finrank F (W n d) := by
  have hli : LinearIndependent F (fun a : {a // a ∈ M n d} => mon (a : E n)) :=
    mon_linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun a : {a // a ∈ M n d} => mon (a : E n))
      = mon '' (M n d : Set (E n)) := by
    ext f; constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
  have := finrank_span_eq_card hli
  rw [hrange] at this
  rw [W, this, Fintype.card_coe]

end Basic

section CLP

/-- Truncated pointwise subtraction of exponent vectors. -/
def asub {n : ℕ} (a b : E n) : E n :=
  fun i => ⟨(a i : ℕ) - (b i : ℕ), by have := (a i).isLt; omega⟩

lemma mem_M_iff {n d : ℕ} (a : E n) : a ∈ M n d ↔ deg a ≤ d := by simp [M]

lemma deg_asub_add {n : ℕ} (a b : E n) (hle : ∀ i, (b i : ℕ) ≤ (a i : ℕ)) :
    deg b + deg (asub a b) = deg a := by
  unfold deg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : ((asub a b) i : ℕ) = (a i : ℕ) - (b i : ℕ) := rfl
  rw [h]; have := hle i; omega

/-- Expansion of a monomial evaluated at a sum. -/
lemma mon_add {n : ℕ} (a : E n) (x y : V n) :
    mon a (x + y) = ∑ b : E n,
      (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) * (mon b x * mon (asub a b) y) := by
  simp only [mon]
  have h1 : ∀ i : Fin n, ((x + y) i) ^ (a i : ℕ) = ∑ j : Fin 3,
      (((a i : ℕ).choose (j : ℕ) : ℕ) : F) * ((x i) ^ (j : ℕ) * (y i) ^ ((a i : ℕ) - (j : ℕ))) := by
    intro i; simpa using binom_expand (a i) (x i) (y i)
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rfl

/-- Functions of two variables of the shape `∑_{deg b ≤ e} mon b (x) w b (y) +
∑_{deg c ≤ e} w' c (x) mon c (y)`: these have "rank" at most `2 * |M n e|`. -/
def Rank1 (n e : ℕ) : Submodule F (V n × V n → F) where
  carrier := {h | ∃ w w' : E n → V n → F, ∀ p : V n × V n,
      h p = (∑ b ∈ M n e, mon b p.1 * w b p.2) + (∑ c ∈ M n e, w' c p.1 * mon c p.2)}
  add_mem' := by
    rintro h1 h2 ⟨w1, w1', e1⟩ ⟨w2, w2', e2⟩
    exact ⟨fun b y => w1 b y + w2 b y, fun c x => w1' c x + w2' c x, fun p => by
      rw [Pi.add_apply, e1, e2]; simp only [mul_add, add_mul, Finset.sum_add_distrib]; ring⟩
  zero_mem' := ⟨0, 0, fun p => by simp⟩
  smul_mem' := by
    rintro t h ⟨w, w', hw⟩
    refine ⟨fun b y => t * w b y, fun c x => t * w' c x, fun p => ?_⟩
    rw [Pi.smul_apply, hw, smul_eq_mul]
    simp only [mul_add, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ => by ring)

lemma Rank1_left {n e : ℕ} {b : E n} (hb : deg b ≤ e) (t : F) (b' : E n) :
    (fun p : V n × V n => t * (mon b p.1 * mon b' p.2)) ∈ Rank1 n e := by
  classical
  refine ⟨fun b'' => if b'' = b then (fun y => t * mon b' y) else 0, 0, fun p => ?_⟩
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single b]
  · simp only [if_true]; ring
  · intro c _ hc; simp [hc]
  · intro hb'; exact absurd ((mem_M_iff b).2 hb) hb'

lemma Rank1_right {n e : ℕ} {b' : E n} (hb : deg b' ≤ e) (t : F) (b : E n) :
    (fun p : V n × V n => t * (mon b p.1 * mon b' p.2)) ∈ Rank1 n e := by
  classical
  refine ⟨0, fun c'' => if c'' = b' then (fun x => t * mon b x) else 0, fun p => ?_⟩
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single b']
  · simp only [if_true]; ring
  · intro c _ hc; simp [hc]
  · intro hb''; exact absurd ((mem_M_iff b').2 hb) hb''

/-- Shifting: the linear map sending `P` to the two-variable function `(x, y) ↦ P (x + y)`. -/
def shiftMap (n : ℕ) : (V n → F) →ₗ[F] (V n × V n → F) where
  toFun P := fun p => P (p.1 + p.2)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Croot–Lev–Pach: if `P` has degree at most `d`, then `(x, y) ↦ P (x + y)` has rank at most
`2 * |M n (d / 2)|`. -/
lemma clp_mem {n d : ℕ} {P : V n → F} (hP : P ∈ W n d) :
    (fun p : V n × V n => P (p.1 + p.2)) ∈ Rank1 n (d / 2) := by
  have key : W n d ≤ Submodule.comap (shiftMap n) (Rank1 n (d / 2)) := by
    rw [W, Submodule.span_le]
    rintro f ⟨a, ha, rfl⟩
    have hda : deg a ≤ d := (mem_M_iff a).1 ha
    show (fun p : V n × V n => mon a (p.1 + p.2)) ∈ Rank1 n (d / 2)
    have hsum : (fun p : V n × V n => mon a (p.1 + p.2))
        = ∑ b : E n, (fun p : V n × V n =>
            (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) * (mon b p.1 * mon (asub a b) p.2)) := by
      funext p
      rw [Finset.sum_apply]
      exact mon_add a p.1 p.2
    rw [hsum]
    refine Submodule.sum_mem _ (fun b _ => ?_)
    by_cases hc : (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) = 0
    · have hz : (fun p : V n × V n =>
          (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) * (mon b p.1 * mon (asub a b) p.2)) = 0 := by
        funext p; rw [hc]; simp
      rw [hz]; exact Submodule.zero_mem _
    · have hc' : (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) ≠ 0 := hc
      have hle : ∀ i, (b i : ℕ) ≤ (a i : ℕ) := by
        intro i
        rw [Finset.prod_ne_zero_iff] at hc'
        have h2 := hc' i (Finset.mem_univ i)
        by_contra hlt
        push_neg at hlt
        rw [Nat.choose_eq_zero_of_lt hlt] at h2
        simp at h2
      have hd := deg_asub_add a b hle
      rcases le_or_gt (deg b) (d / 2) with h | h
      · exact Rank1_left h _ _
      · exact Rank1_right (by omega) _ _
  exact key hP

/-- The rank bound: a two-variable function in `Rank1 n e` which is "diagonal" on `S × S` with
nonzero diagonal entries forces `|S| ≤ 2 * |M n e|`. -/
lemma rank_bound {n e : ℕ} {h : V n × V n → F} (hh : h ∈ Rank1 n e)
    {S : Finset (V n)} (hdiag : ∀ x ∈ S, h (x, x) ≠ 0)
    (hoff : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → h (x, y) = 0) :
    S.card ≤ 2 * (M n e).card := by
  classical
  obtain ⟨w, w', hw⟩ := hh
  by_contra hcon
  push_neg at hcon
  have hnli : ¬ LinearIndependent F (fun x : {x : V n // x ∈ S} =>
      (Sum.elim (fun b : {a : E n // a ∈ M n e} => mon (b : E n) (x : V n))
        (fun c : {a : E n // a ∈ M n e} => w' (c : E n) (x : V n)) :
        ({a : E n // a ∈ M n e} ⊕ {a : E n // a ∈ M n e}) → F)) := by
    intro hli
    have hcc := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_coe,
      Fintype.card_coe] at hcc
    omega
  rw [Fintype.not_linearIndependent_iff] at hnli
  obtain ⟨g, hg, x₀, hx₀⟩ := hnli
  have hcoordl : ∀ b ∈ M n e, ∑ x : {x : V n // x ∈ S}, g x * mon b (x : V n) = 0 := by
    intro b hb
    have := congrFun hg (Sum.inl ⟨b, hb⟩)
    simpa [Finset.sum_apply] using this
  have hcoordr : ∀ c ∈ M n e, ∑ x : {x : V n // x ∈ S}, g x * w' c (x : V n) = 0 := by
    intro c hc
    have := congrFun hg (Sum.inr ⟨c, hc⟩)
    simpa [Finset.sum_apply] using this
  have hzero : ∑ x : {x : V n // x ∈ S}, g x * h ((x : V n), (x₀ : V n)) = 0 := by
    have hexp : ∀ x : {x : V n // x ∈ S}, g x * h ((x : V n), (x₀ : V n))
        = (∑ b ∈ M n e, g x * (mon b (x : V n) * w b (x₀ : V n)))
          + (∑ c ∈ M n e, g x * (w' c (x : V n) * mon c (x₀ : V n))) := by
      intro x
      rw [hw ((x : V n), (x₀ : V n))]
      simp [Finset.mul_sum, mul_add]
    calc ∑ x : {x : V n // x ∈ S}, g x * h ((x : V n), (x₀ : V n))
        = ∑ x : {x : V n // x ∈ S}, ((∑ b ∈ M n e, g x * (mon b (x : V n) * w b (x₀ : V n)))
          + (∑ c ∈ M n e, g x * (w' c (x : V n) * mon c (x₀ : V n)))) :=
          Finset.sum_congr rfl (fun x _ => hexp x)
      _ = (∑ x : {x : V n // x ∈ S}, ∑ b ∈ M n e, g x * (mon b (x : V n) * w b (x₀ : V n)))
          + (∑ x : {x : V n // x ∈ S}, ∑ c ∈ M n e, g x * (w' c (x : V n) * mon c (x₀ : V n))) :=
          Finset.sum_add_distrib
      _ = (∑ b ∈ M n e, ∑ x : {x : V n // x ∈ S}, g x * (mon b (x : V n) * w b (x₀ : V n)))
          + (∑ c ∈ M n e, ∑ x : {x : V n // x ∈ S}, g x * (w' c (x : V n) * mon c (x₀ : V n))) := by
          congr 1 <;> exact Finset.sum_comm
      _ = 0 := by
          have h1 : ∀ b ∈ M n e,
              (∑ x : {x : V n // x ∈ S}, g x * (mon b (x : V n) * w b (x₀ : V n))) = 0 := by
            intro b hb
            have hrw : ∀ x : {x : V n // x ∈ S}, g x * (mon b (x : V n) * w b (x₀ : V n))
                = (g x * mon b (x : V n)) * w b (x₀ : V n) := fun x => by ring
            rw [Finset.sum_congr rfl (fun x _ => hrw x), ← Finset.sum_mul, hcoordl b hb, zero_mul]
          have h2 : ∀ c ∈ M n e,
              (∑ x : {x : V n // x ∈ S}, g x * (w' c (x : V n) * mon c (x₀ : V n))) = 0 := by
            intro c hc
            have hrw : ∀ x : {x : V n // x ∈ S}, g x * (w' c (x : V n) * mon c (x₀ : V n))
                = (g x * w' c (x : V n)) * mon c (x₀ : V n) := fun x => by ring
            rw [Finset.sum_congr rfl (fun x _ => hrw x), ← Finset.sum_mul, hcoordr c hc, zero_mul]
          rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
          simp
  rw [Finset.sum_eq_single x₀] at hzero
  · exact (mul_ne_zero hx₀ (hdiag (x₀ : V n) x₀.2)) hzero
  · intro x _ hne
    rw [hoff (x : V n) x.2 (x₀ : V n) x₀.2 (fun heq => hne (Subtype.ext heq)), mul_zero]
  · intro hmem; exact absurd (Finset.mem_univ x₀) hmem

end CLP

section Support

/-- A subspace of functions admits a "separating" set of points of size at most its dimension. -/
lemma exists_sep_set {n : ℕ} : ∀ (k : ℕ) (Ws : Submodule F (V n → F)), Module.finrank F Ws = k →
    ∃ U : Finset (V n), U.card ≤ k ∧ ∀ P ∈ Ws, (∀ u ∈ U, P u = 0) → P = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Ws hrank
    by_cases hbot : Ws = ⊥
    · refine ⟨∅, by simp, fun P hP _ => ?_⟩
      rw [hbot, Submodule.mem_bot] at hP; exact hP
    · obtain ⟨P₀, hP₀mem, hP₀ne⟩ : ∃ P₀ ∈ Ws, P₀ ≠ 0 := by
        have hbot' : Ws ≠ ⊥ := hbot
        rw [Submodule.ne_bot_iff] at hbot'
        obtain ⟨P₀, h1, h2⟩ := hbot'; exact ⟨P₀, h1, h2⟩
      obtain ⟨v, hv⟩ : ∃ v, P₀ v ≠ 0 := Function.ne_iff.1 hP₀ne
      set Kv : Submodule F (V n → F) :=
        LinearMap.ker (LinearMap.proj v : (V n → F) →ₗ[F] F)
      have hlt : Ws ⊓ Kv < Ws := by
        refine lt_of_le_of_ne inf_le_left (fun heq => hv ?_)
        have hmem : P₀ ∈ Ws ⊓ Kv := by rw [heq]; exact hP₀mem
        exact hmem.2
      have hk' : Module.finrank F (Ws ⊓ Kv : Submodule F (V n → F)) < k := by
        rw [← hrank]; exact Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨U', hcard', hsep'⟩ := ih _ hk' (Ws ⊓ Kv) rfl
      refine ⟨insert v U', ?_, ?_⟩
      · have := Finset.card_insert_le v U'
        omega
      · intro P hP hzero
        exact hsep' P ⟨hP, hzero v (Finset.mem_insert_self v U')⟩
          (fun u hu => hzero u (Finset.mem_insert_of_mem hu))

/-- A subspace of functions contains an element whose support has size at least the dimension. -/
lemma exists_large_support {n : ℕ} (Ws : Submodule F (V n → F)) :
    ∃ P ∈ Ws, Module.finrank F Ws ≤ (Finset.univ.filter (fun x : V n => P x ≠ 0)).card := by
  classical
  obtain ⟨U, hcard, hsep⟩ := exists_sep_set (Module.finrank F Ws) Ws rfl
  set r : Ws →ₗ[F] ({u : V n // u ∈ U} → F) :=
    { toFun := fun P u => (P : V n → F) (u : V n)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } with hr
  have hinj : Function.Injective r := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have hz : (P : V n → F) = 0 := hsep _ P.2 (fun u hu => congrFun hP ⟨u, hu⟩)
    exact Subtype.ext hz
  have hfr : Module.finrank F ({u : V n // u ∈ U} → F) = U.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hle : Module.finrank F Ws ≤ U.card := by
    have := LinearMap.finrank_le_finrank_of_injective (f := r) hinj
    rwa [hfr] at this
  have heq : Module.finrank F Ws = Module.finrank F ({u : V n // u ∈ U} → F) := by
    rw [hfr]; omega
  have hsurj : Function.Surjective r :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
  obtain ⟨P, hP⟩ := hsurj 1
  refine ⟨(P : V n → F), P.2, ?_⟩
  have hsub : U ⊆ Finset.univ.filter (fun x : V n => (P : V n → F) x ≠ 0) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : (P : V n → F) u = 1 := congrFun hP ⟨u, hu⟩
    rw [h1]; exact one_ne_zero
  calc Module.finrank F Ws ≤ U.card := hle
    _ ≤ _ := Finset.card_le_card hsub

end Support

section Main

/-- The flip map on exponent vectors, `a ↦ 2 - a`. -/
def flipE {n : ℕ} (a : E n) : E n := fun i => ⟨2 - (a i : ℕ), by omega⟩

lemma deg_flipE {n : ℕ} (a : E n) : deg (flipE a) + deg a = 2 * n := by
  unfold deg
  rw [← Finset.sum_add_distrib]
  have h : ∀ i : Fin n, ((flipE a) i : ℕ) + (a i : ℕ) = 2 := by
    intro i; have := (a i).isLt
    show 2 - (a i : ℕ) + (a i : ℕ) = 2
    omega
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp [mul_comm]

lemma flipE_injective {n : ℕ} : Function.Injective (flipE (n := n)) := by
  intro a b hab
  funext i
  have h := congrArg (fun c : E n => ((c i : Fin 3) : ℕ)) hab
  have h1 : 2 - (a i : ℕ) = 2 - (b i : ℕ) := h
  have ha := (a i).isLt
  have hb := (b i).isLt
  exact Fin.ext (by omega)

lemma card_E (n : ℕ) : Fintype.card (E n) = 3 ^ n := by
  show Fintype.card (Fin n → Fin 3) = 3 ^ n
  simp

lemma card_compl_M_le {n : ℕ} :
    (Finset.univ \ M n (4 * n / 3)).card ≤ (M n (2 * n / 3)).card := by
  refine Finset.card_le_card_of_injOn flipE ?_ (fun a _ b _ h => flipE_injective h)
  intro a ha
  simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_M_iff] at ha ⊢
  have h := deg_flipE a
  omega

lemma M_mono {n : ℕ} {d d' : ℕ} (h : d ≤ d') : M n d ⊆ M n d' := by
  intro a ha
  rw [mem_M_iff] at *
  omega

/-- Restriction of a function to the complement of a finite set. -/
def restrMap {n : ℕ} (T : Finset (V n)) : (V n → F) →ₗ[F] ({x : V n // x ∉ T} → F) where
  toFun f := fun x => f (x : V n)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma neg_eq_add_self {n : ℕ} (x : V n) : x + x = -x := by
  have h : ∀ u : ZMod 3, u + u = -u := by decide
  funext i; exact h (x i)

/-- **The Ellenberg–Gijswijt bound**: a subset of `𝔽₃ⁿ` without three-term arithmetic
progressions has size at most `3` times the number of exponent vectors of degree at most
`2n/3`. -/
theorem capset_card_le {n : ℕ} (A : Finset (V n)) (hA : ThreeAPFree (A : Set (V n))) :
    A.card ≤ 3 * (M n (2 * n / 3)).card := by
  classical
  set d := 4 * n / 3 with hd
  set T : Finset (V n) := A.image (fun a => -a) with hT
  have hfrX : Module.finrank F (V n → F) = 3 ^ n := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have hTcard : T.card = A.card := Finset.card_image_of_injective _ neg_injective
  have hAle : A.card ≤ 3 ^ n := by
    have h : A.card ≤ Fintype.card (V n) := Finset.card_le_univ A
    simpa using h
  have hcompl : Fintype.card {x : V n // x ∉ T} = 3 ^ n - A.card := by
    rw [Fintype.card_subtype]
    have h : (Finset.univ.filter (fun x : V n => x ∉ T)) = Tᶜ := by ext x; simp
    rw [h, Finset.card_compl, hTcard]
    simp
  -- lower bound for the dimension of `W n d ⊓ ker`
  have hKrank : 3 ^ n ≤ Module.finrank F ↥(LinearMap.ker (restrMap T)) + (3 ^ n - A.card) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (restrMap T)
    have h2 : Module.finrank F ↥(LinearMap.range (restrMap T)) ≤ 3 ^ n - A.card := by
      have h3 := Submodule.finrank_le (LinearMap.range (restrMap T))
      rwa [Module.finrank_fintype_fun_eq_card, hcompl] at h3
    rw [hfrX] at h1
    omega
  have hinf := Submodule.finrank_sup_add_finrank_inf_eq (W n d) (LinearMap.ker (restrMap T))
  have hsuple : Module.finrank F ↥(W n d ⊔ LinearMap.ker (restrMap T)) ≤ 3 ^ n := by
    have h := Submodule.finrank_le (W n d ⊔ LinearMap.ker (restrMap T))
    rwa [hfrX] at h
  have hWrank : (M n d).card ≤ Module.finrank F ↥(W n d) := card_M_le_finrank_W n d
  have hWsrank : (M n d).card
      ≤ Module.finrank F ↥(W n d ⊓ LinearMap.ker (restrMap T)) + (3 ^ n - A.card) := by
    omega
  -- a polynomial with large support
  obtain ⟨P, hPmem, hPsupp⟩ := exists_large_support (W n d ⊓ LinearMap.ker (restrMap T))
  have hPW : P ∈ W n d := hPmem.1
  have hPK : ∀ x : V n, x ∉ T → P x = 0 := by
    intro x hx
    have h : (restrMap T) P = 0 := hPmem.2
    exact congrFun h ⟨x, hx⟩
  set S : Finset (V n) := A.filter (fun x => P (x + x) ≠ 0) with hS
  -- the support of `P` is contained in `-S`
  have hsuppS : (Finset.univ.filter (fun x : V n => P x ≠ 0)).card ≤ S.card := by
    have hsub : (Finset.univ.filter (fun x : V n => P x ≠ 0)) ⊆ S.image (fun a => -a) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      by_cases hxT : x ∈ T
      · rw [hT] at hxT
        obtain ⟨a, haA, hax⟩ := Finset.mem_image.1 hxT
        refine Finset.mem_image.2 ⟨a, ?_, hax⟩
        rw [hS, Finset.mem_filter]
        refine ⟨haA, ?_⟩
        rw [neg_eq_add_self a, hax]
        exact hx
      · exact absurd (hPK x hxT) hx
    calc (Finset.univ.filter (fun x : V n => P x ≠ 0)).card ≤ (S.image (fun a => -a)).card :=
          Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
  -- the rank bound applies to `S`
  have hSbound : S.card ≤ 2 * (M n (d / 2)).card := by
    refine rank_bound (clp_mem hPW) ?_ ?_
    · intro x hx
      rw [hS, Finset.mem_filter] at hx
      exact hx.2
    · intro x hx y hy hne
      by_contra hxy
      have hxT : x + y ∈ T := by
        by_contra hnot
        exact hxy (hPK _ hnot)
      rw [hT] at hxT
      obtain ⟨c, hcA, hc⟩ := Finset.mem_image.1 hxT
      have hxA : x ∈ A := (Finset.mem_filter.1 (hS ▸ hx)).1
      have hyA : y ∈ A := (Finset.mem_filter.1 (hS ▸ hy)).1
      have hsum : x + y = c + c := by rw [neg_eq_add_self c, hc]
      have h1 : x = c := hA hxA hcA hyA hsum
      have h2 : y = c := hA hyA hcA hxA (by rw [add_comm]; exact hsum)
      exact hne (h1.trans h2.symm)
  -- putting things together
  have hde : d / 2 ≤ 2 * n / 3 := by omega
  have hMe : (M n (d / 2)).card ≤ (M n (2 * n / 3)).card :=
    Finset.card_le_card (M_mono hde)
  have hcompM : 3 ^ n ≤ (M n d).card + (M n (2 * n / 3)).card := by
    have h1 : (Finset.univ \ M n d).card ≤ (M n (2 * n / 3)).card := card_compl_M_le
    have h2 : (Finset.univ \ M n d).card + (M n d).card = (Finset.univ : Finset (E n)).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
    have h4 : (Finset.univ : Finset (E n)).card = 3 ^ n := by
      simp
    omega
  omega

end Main

section Counting

/-- The generating identity `∑_a (1/2)^{deg a} = (7/4)^n`. -/
lemma sum_half_pow_deg (n : ℕ) : ∑ a : E n, ((1 : ℚ) / 2) ^ (deg a) = (7 / 4) ^ n := by
  have h1 : ∀ a : E n, ((1 : ℚ) / 2) ^ (deg a) = ∏ i, ((1 : ℚ) / 2) ^ ((a i : ℕ)) := by
    intro a; rw [deg, Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  have key := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 3)))
    (fun (_ : Fin n) (j : Fin 3) => ((1 : ℚ) / 2) ^ (j : ℕ))
  rw [Fintype.piFinset_univ] at key
  rw [← key]
  have h2 : ∀ i : Fin n, (∑ j : Fin 3, ((1 : ℚ) / 2) ^ ((j : ℕ))) = 7 / 4 := by
    intro i; rw [Fin.sum_univ_three]; norm_num
  rw [Finset.prod_congr rfl (fun i _ => h2 i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

lemma card_M_bound (n d : ℕ) : ((M n d).card : ℚ) * ((1 : ℚ) / 2) ^ d ≤ (7 / 4) ^ n := by
  rw [← sum_half_pow_deg n]
  calc ((M n d).card : ℚ) * ((1 : ℚ) / 2) ^ d = ∑ _a ∈ M n d, ((1 : ℚ) / 2) ^ d := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ M n d, ((1 : ℚ) / 2) ^ (deg a) := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) ((mem_M_iff a).1 ha)
    _ ≤ ∑ a : E n, ((1 : ℚ) / 2) ^ (deg a) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
        intro i _ _; positivity

/-- The number of exponent vectors of degree at most `2n/3` is exponentially smaller than `3ⁿ`:
`m³ · 64ⁿ ≤ 1372ⁿ`, and `1372 < 64 · 27`. -/
lemma card_M_pow_le (n : ℕ) : ((M n (2 * n / 3)).card) ^ 3 * 64 ^ n ≤ 1372 ^ n := by
  have h := card_M_bound n (2 * n / 3)
  set m : ℕ := (M n (2 * n / 3)).card with hm
  have hpos : (0 : ℚ) < ((1 : ℚ) / 2) ^ (2 * n / 3) := by positivity
  have h2 : (m : ℚ) ≤ 2 ^ (2 * n / 3) * (7 / 4) ^ n := by
    rw [← le_div_iff₀ hpos] at h
    have hkey : ((1 : ℚ) / 2) ^ (2 * n / 3) = 1 / 2 ^ (2 * n / 3) := by rw [div_pow, one_pow]
    have hkey2 : (7 / 4 : ℚ) ^ n / (1 / (2 : ℚ) ^ (2 * n / 3))
        = (7 / 4 : ℚ) ^ n * 2 ^ (2 * n / 3) := by field_simp
    rw [hkey, hkey2] at h
    calc (m : ℚ) ≤ (7 / 4) ^ n * 2 ^ (2 * n / 3) := h
      _ = 2 ^ (2 * n / 3) * (7 / 4) ^ n := by ring
  have h3 : (m : ℚ) ^ 3 ≤ (2 ^ (2 * n / 3)) ^ 3 * ((7 / 4) ^ n) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 3
  have h4 : ((2 : ℚ) ^ (2 * n / 3)) ^ 3 ≤ 4 ^ n := by
    rw [← pow_mul]
    calc (2 : ℚ) ^ (2 * n / 3 * 3) ≤ 2 ^ (2 * n) := by
          apply pow_le_pow_right₀ (by norm_num); omega
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  have h5 : (m : ℚ) ^ 3 * 64 ^ n ≤ 1372 ^ n := by
    have h6 : ((7 / 4 : ℚ) ^ n) ^ 3 = (343 / 64 : ℚ) ^ n := by
      rw [← pow_mul, mul_comm n 3, pow_mul]; norm_num
    calc (m : ℚ) ^ 3 * 64 ^ n ≤ ((2 ^ (2 * n / 3)) ^ 3 * ((7 / 4) ^ n) ^ 3) * 64 ^ n :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ (4 ^ n * (343 / 64 : ℚ) ^ n) * 64 ^ n := by
          rw [h6]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h4 (by positivity)) (by positivity)
      _ = 1372 ^ n := by rw [← mul_pow, ← mul_pow]; norm_num
  have hfin : (((m ^ 3 * 64 ^ n : ℕ)) : ℚ) ≤ ((1372 ^ n : ℕ) : ℚ) := by push_cast; exact h5
  exact_mod_cast hfin

end Counting

section Asymptotic

open Filter

/-- The maximal size of a subset of `𝔽₃ⁿ` containing no three-term arithmetic progression
(a *cap set*). -/
noncomputable def capSetMax (n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset (V n), ThreeAPFree (A : Set (V n)) ∧ A.card = k}

lemma capSetMax_bddAbove (n : ℕ) :
    BddAbove {k | ∃ A : Finset (V n), ThreeAPFree (A : Set (V n)) ∧ A.card = k} := by
  refine ⟨3 ^ n, ?_⟩
  rintro k ⟨A, -, rfl⟩
  have h : A.card ≤ Fintype.card (V n) := Finset.card_le_univ A
  simpa using h

/-- `capSetMax n` is an upper bound for the size of any cap set in `𝔽₃ⁿ`. -/
lemma le_capSetMax {n : ℕ} (A : Finset (V n)) (hA : ThreeAPFree (A : Set (V n))) :
    A.card ≤ capSetMax n :=
  le_csSup (capSetMax_bddAbove n) ⟨A, hA, rfl⟩

lemma capSetMax_le (n : ℕ) : capSetMax n ≤ 3 * (M n (2 * n / 3)).card := by
  refine csSup_le ⟨0, ⟨∅, by simp, by simp⟩⟩ ?_
  rintro k ⟨A, hA, rfl⟩
  exact capset_card_le A hA

lemma capSetMax_pow_le (n : ℕ) : (capSetMax n) ^ 3 * 64 ^ n ≤ 27 * 1372 ^ n := by
  have h1 := capSetMax_le n
  have h2 := card_M_pow_le n
  calc (capSetMax n) ^ 3 * 64 ^ n ≤ (3 * (M n (2 * n / 3)).card) ^ 3 * 64 ^ n :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h1 3)
    _ = 27 * (((M n (2 * n / 3)).card) ^ 3 * 64 ^ n) := by ring
    _ ≤ 27 * 1372 ^ n := Nat.mul_le_mul_left _ h2

lemma capSetMax_div_cube_le (n : ℕ) :
    ((capSetMax n : ℝ) / 3 ^ n) ^ 3 ≤ 27 * (1372 / 1728 : ℝ) ^ n := by
  have hnat := capSetMax_pow_le n
  have hR : ((capSetMax n : ℝ)) ^ 3 * 64 ^ n ≤ 27 * 1372 ^ n := by exact_mod_cast hnat
  have h27 : ((3 : ℝ) ^ n) ^ 3 = 27 ^ n := by
    rw [← pow_mul, mul_comm n 3, pow_mul]; norm_num
  have hsplit : (1372 / 1728 : ℝ) ^ n = 1372 ^ n / (64 ^ n * 27 ^ n) := by
    rw [div_pow, ← mul_pow]; norm_num
  rw [div_pow, h27, div_le_iff₀ (by positivity), hsplit]
  have h64 : (0 : ℝ) < 64 ^ n := by positivity
  rw [show (27 : ℝ) * (1372 ^ n / (64 ^ n * 27 ^ n)) * 27 ^ n
      = 27 * 1372 ^ n / 64 ^ n by field_simp, le_div_iff₀ h64]
  exact hR

/-- The density of a maximal cap set in `𝔽₃ⁿ` tends to `0`. -/
theorem capSetMax_div_tendsto :
    Tendsto (fun n : ℕ => (capSetMax n : ℝ) / 3 ^ n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hr : Tendsto (fun n : ℕ => (27 : ℝ) * (1372 / 1728 : ℝ) ^ n) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1372 / 1728 : ℝ))
      (by norm_num) (by norm_num)
    simpa using h.const_mul (27 : ℝ)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hr) (ε ^ 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hnn : 0 ≤ (capSetMax n : ℝ) / 3 ^ n := by positivity
  have hlt : ((capSetMax n : ℝ) / 3 ^ n) ^ 3 < ε ^ 3 := by
    refine lt_of_le_of_lt (capSetMax_div_cube_le n) ?_
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    calc (27 : ℝ) * (1372 / 1728 : ℝ) ^ n ≤ |(27 : ℝ) * (1372 / 1728 : ℝ) ^ n| :=
          le_abs_self _
      _ < ε ^ 3 := h
  have hfin : (capSetMax n : ℝ) / 3 ^ n < ε := by
    by_contra hge
    push_neg at hge
    exact absurd hlt (not_lt.2 (pow_le_pow_left₀ (le_of_lt hε) hge 3))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact hfin

end Asymptotic

end CapSet

/-- **The cap set theorem** (Croot–Lev–Pach, Ellenberg–Gijswijt): subsets of `𝔽₃ⁿ` containing no
three-term arithmetic progression have size `o(3ⁿ)`. -/
theorem cap_set :
    (fun n : ℕ => (CapSet.capSetMax n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (3 : ℝ) ^ n) := by
  rw [Asymptotics.isLittleO_iff_tendsto (fun n hn => absurd hn (by positivity))]
  exact CapSet.capSetMax_div_tendsto

/-- Uniform quantitative form of the cap set theorem: for every `ε > 0`, all sufficiently large
`n`, and every three-term-progression-free `A ⊆ 𝔽₃ⁿ`, we have `|A| ≤ ε · 3ⁿ`. -/
theorem cap_set_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (A.card : ℝ) ≤ ε * 3 ^ n := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 CapSet.capSetMax_div_tendsto ε hε
  refine ⟨N, fun n hn A hA => ?_⟩
  have h1 : (A.card : ℝ) ≤ (CapSet.capSetMax n : ℝ) := by
    exact_mod_cast CapSet.le_capSetMax A hA
  have h2 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  have h3 : (CapSet.capSetMax n : ℝ) ≤ ε * 3 ^ n := by
    rw [← div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ n)] at *
    exact le_of_lt h2
  linarith

end Math2

import Mathlib
import RequestProject.CapSet

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

