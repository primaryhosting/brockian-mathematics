/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace CS

/-! ### Basic probabilistic vocabulary

All probabilities are uniform probabilities over finite types, expressed as expectations
of `{0,1}`-valued indicator functions. -/

/-- The `{0,1}`-valued indicator of a boolean. -/
noncomputable def ind (b : Bool) : ℝ := if b then 1 else 0

/-- The probability that the predicate `p` holds for a uniformly random element of the
finite type `α`. -/
noncomputable def pr {α : Type*} [Fintype α] (p : α → Bool) : ℝ := 𝔼 a, ind (p a)

/-! ### The Nisan–Wigderson generator -/

/-- The Nisan–Wigderson generator built from a combinatorial design `S` (given by `m` injective
maps `Fin n → Fin ℓ`, i.e. `m` subsets of size `n` of the `ℓ` seed bits) and a hard function
`f : (Fin n → Bool) → Bool`.  On seed `x` it outputs the `m` bits `f (x restricted to Sᵢ)`. -/
def nwGen {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (x : Fin ℓ → Bool) : Fin m → Bool := fun i => f fun k => x (S i k)

/-- `u` depends on at most `d` of its `n` input bits. -/
def IsJunta {n : ℕ} (d : ℕ) (u : (Fin n → Bool) → Bool) : Prop :=
  ∃ T : Finset (Fin n), T.card ≤ d ∧
    ∀ z z' : Fin n → Bool, (∀ k ∈ T, z k = z' k) → u z = u z'

/-- The class of *next-bit predictors* arising from the distinguisher `D` in the
Nisan–Wigderson argument at hybrid step `t`: a predictor is obtained by feeding `D` with
`d`-juntas of the input `z` in the first `t` coordinates, hard-wired advice bits in the
remaining coordinates, and possibly negating the output. -/
def IsNWPredictor {n m : ℕ} (d : ℕ) (D : (Fin m → Bool) → Bool) (t : ℕ)
    (g : (Fin n → Bool) → Bool) : Prop :=
  ∃ (u : Fin m → (Fin n → Bool) → Bool) (w : Fin m → Bool) (b : Bool),
    (∀ j, IsJunta d (u j)) ∧
    ∀ z, g z = xor b (D fun j => if (j : ℕ) < t then u j z else w j)

/-- The `t`-th hybrid distribution: the first `t` output bits come from the generator,
the remaining ones are uniformly random. -/
def hyb {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool) (t : ℕ)
    (x : Fin ℓ → Bool) (y : Fin m → Bool) : Fin m → Bool :=
  fun i => if (i : ℕ) < t then nwGen S f x i else y i

/-- Probability that `D` accepts the `t`-th hybrid. -/
noncomputable def hybProb {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) (t : ℕ) : ℝ :=
  pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) => D (hyb S f t p.1 p.2)

/-- Overwrite the coordinates in the range of `σ` of `x0` by the bits of `z`. -/
noncomputable def glue {n ℓ : ℕ} (σ : Fin n → Fin ℓ) (z : Fin n → Bool) (x0 : Fin ℓ → Bool) :
    Fin ℓ → Bool :=
  fun i => if h : ∃ k, σ k = i then z h.choose else x0 i

/-! ### Auxiliary lemmas -/

lemma glue_apply_mem {n ℓ : ℕ} {σ : Fin n → Fin ℓ} (hσ : Function.Injective σ)
    (z : Fin n → Bool) (x0 : Fin ℓ → Bool) (k : Fin n) : glue σ z x0 (σ k) = z k := by
  have h : ∃ k', σ k' = σ k := ⟨k, rfl⟩
  simp only [glue, dif_pos h]
  congr 1
  exact hσ h.choose_spec

lemma glue_apply_not_mem {n ℓ : ℕ} {σ : Fin n → Fin ℓ}
    (z : Fin n → Bool) (x0 : Fin ℓ → Bool) {i : Fin ℓ} (hi : ∀ k, σ k ≠ i) :
    glue σ z x0 i = x0 i := by
  simp only [glue]
  rw [dif_neg]
  rintro ⟨k, hk⟩
  exact hi k hk

/-- The seed-splitting equivalence: a seed together with a block assignment can be traded for
a block assignment together with a seed. -/
noncomputable def glueEquiv {n ℓ : ℕ} {σ : Fin n → Fin ℓ} (hσ : Function.Injective σ) :
    ((Fin n → Bool) × (Fin ℓ → Bool)) ≃ ((Fin ℓ → Bool) × (Fin n → Bool)) where
  toFun p := (glue σ p.1 p.2, fun k => p.2 (σ k))
  invFun q := (fun k => q.1 (σ k), glue σ q.2 q.1)
  left_inv := by
    rintro ⟨z, x0⟩
    refine Prod.ext (funext fun k => glue_apply_mem hσ z x0 k) ?_
    simp only
    funext i
    by_cases h : ∃ k, σ k = i
    · obtain ⟨k, rfl⟩ := h
      simp [glue_apply_mem hσ]
    · push_neg at h
      rw [glue_apply_not_mem _ _ h, glue_apply_not_mem _ _ h]
  right_inv := by
    rintro ⟨x, v⟩
    refine Prod.ext ?_ (funext fun k => glue_apply_mem hσ v x k)
    simp only
    funext i
    by_cases h : ∃ k, σ k = i
    · obtain ⟨k, rfl⟩ := h
      simp [glue_apply_mem hσ]
    · push_neg at h
      rw [glue_apply_not_mem _ _ h, glue_apply_not_mem _ _ h]

/-- Averaging over the seed can be done by first averaging over the bits sitting in the
range of an injective map `σ` and then over the remaining bits. -/
lemma expect_glue {n ℓ : ℕ} {σ : Fin n → Fin ℓ} (hσ : Function.Injective σ)
    (F : (Fin ℓ → Bool) → ℝ) :
    (𝔼 (x : Fin ℓ → Bool), F x) = 𝔼 (z : Fin n → Bool), 𝔼 (x0 : Fin ℓ → Bool), F (glue σ z x0) := by
  have h1 : (𝔼 (p : (Fin n → Bool) × (Fin ℓ → Bool)), F (glue σ p.1 p.2))
      = 𝔼 (z : Fin n → Bool), 𝔼 (x0 : Fin ℓ → Bool), F (glue σ z x0) := by
    have h := Finset.expect_product' (univ : Finset (Fin n → Bool))
      (univ : Finset (Fin ℓ → Bool)) fun z x0 => F (glue σ z x0)
    rw [Finset.univ_product_univ] at h
    exact h
  have h2 : (𝔼 (p : (Fin n → Bool) × (Fin ℓ → Bool)), F (glue σ p.1 p.2))
      = 𝔼 (q : (Fin ℓ → Bool) × (Fin n → Bool)), F q.1 :=
    Finset.expect_equiv (glueEquiv hσ) (by simp) fun p _ => rfl
  have h3 : (𝔼 (q : (Fin ℓ → Bool) × (Fin n → Bool)), F q.1) = 𝔼 (x : Fin ℓ → Bool), F x := by
    have h := Finset.expect_product' (univ : Finset (Fin ℓ → Bool))
      (univ : Finset (Fin n → Bool)) fun x _v => F x
    rw [Finset.univ_product_univ] at h
    rw [h]
    exact Finset.expect_congr rfl fun x _ => Finset.expect_const univ_nonempty _
  rw [← h1, h2, h3]

/-- Averaging over a boolean vector equals averaging the two possible values of one coordinate. -/
lemma expect_update_bool {m : ℕ} (it : Fin m) (H : (Fin m → Bool) → ℝ) :
    (𝔼 (y : Fin m → Bool), H y)
      = 𝔼 (y : Fin m → Bool), (H (Function.update y it true) + H (Function.update y it false)) / 2 := by
  have hinv : Function.Involutive (fun y : Fin m → Bool => Function.update y it (!(y it))) := by
    intro y
    funext i
    by_cases h : i = it <;> simp [Function.update, h]
  set e : Equiv.Perm (Fin m → Bool) := hinv.toPerm _ with he
  have h1 : (𝔼 (y : Fin m → Bool), H (e y)) = 𝔼 (y : Fin m → Bool), H y :=
    Finset.expect_equiv e (by simp) (fun y _ => rfl)
  have h2 : ∀ y : Fin m → Bool,
      (H (Function.update y it true) + H (Function.update y it false)) / 2
        = (H y + H (e y)) / 2 := by
    intro y
    have hy : Function.update y it (y it) = y := by simp
    cases hyt : y it
    · have h3 : e y = Function.update y it true := by
        simp [he, Function.Involutive.toPerm, hyt]
      rw [h3, show Function.update y it false = y by rw [← hyt]; exact hy]
      ring
    · have h3 : e y = Function.update y it false := by
        simp [he, Function.Involutive.toPerm, hyt]
      rw [h3, show Function.update y it true = y by rw [← hyt]; exact hy]
  rw [Finset.expect_congr rfl (fun y _ => h2 y)]
  have h4 : (𝔼 (y : Fin m → Bool), (H y + H (e y)) / 2)
      = ((𝔼 (y : Fin m → Bool), H y) + 𝔼 (y : Fin m → Bool), H (e y)) / 2 := by
    rw [← Finset.expect_add_distrib, ← Finset.expect_div]
  rw [h4, h1]
  ring

lemma exists_ge_expect {α : Type*} [Fintype α] [Nonempty α] (F : α → ℝ) :
    ∃ a, (𝔼 x, F x) ≤ F a := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (univ : Finset α) F univ_nonempty
  exact ⟨a, Finset.expect_le univ_nonempty fun x _ => ha x (mem_univ x)⟩

/-- Averaging over a product type. -/
lemma pr_prod {α β : Type*} [Fintype α] [Fintype β] (p : α × β → Bool) :
    pr p = 𝔼 a, 𝔼 b, ind (p (a, b)) := by
  refine Eq.trans ?_ (Finset.expect_product' univ univ fun a b => ind (p (a, b)))
  rw [Finset.univ_product_univ]
  rfl

/-! ### The hybrid argument -/

lemma hybProb_zero {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) : hybProb S f D 0 = pr D := by
  rw [hybProb, pr_prod]
  have h : ∀ (x : Fin ℓ → Bool) (y : Fin m → Bool), hyb S f 0 x y = y := by
    intro x y; funext i; simp [hyb]
  simp only [h]
  rw [Finset.expect_const univ_nonempty]
  rfl

lemma hybProb_card {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) : hybProb S f D m = pr fun x => D (nwGen S f x) := by
  rw [hybProb, pr_prod]
  have h : ∀ (x : Fin ℓ → Bool) (y : Fin m → Bool), hyb S f m x y = nwGen S f x := by
    intro x y; funext i; simp [hyb, i.isLt]
  simp only [h]
  refine Finset.expect_congr rfl fun x _ => ?_
  rw [Finset.expect_const univ_nonempty]

lemma hyb_succ {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    {t : ℕ} (ht : t < m) (x : Fin ℓ → Bool) (y : Fin m → Bool) :
    hyb S f (t + 1) x y
      = hyb S f t x (Function.update y ⟨t, ht⟩ (nwGen S f x ⟨t, ht⟩)) := by
  funext i
  simp only [hyb]
  rcases lt_trichotomy (i : ℕ) t with h | h | h
  · simp [h, Nat.lt_succ_of_lt h]
  · have hi : i = (⟨t, ht⟩ : Fin m) := Fin.ext h
    subst hi
    simp
  · have hne : i ≠ (⟨t, ht⟩ : Fin m) := by
      intro hh; rw [hh] at h; exact absurd h (lt_irrefl t)
    have h1 : ¬ ((i : ℕ) < t + 1) := by omega
    simp [h1, Nat.not_lt.mpr h.le, Function.update_of_ne hne]

/-- Yao's next-bit predictor step: the hybrid gap at step `t` is exactly the advantage of the
predictor built from `D`. -/
lemma yao_predictor {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) {t : ℕ} (ht : t < m) :
    (pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
        (xor (!(p.2 ⟨t, ht⟩)) (D (hyb S f t p.1 p.2))
          == nwGen S f p.1 ⟨t, ht⟩))
      = 1 / 2 + (hybProb S f D (t + 1) - hybProb S f D t) := by
  have key : ∀ x : Fin ℓ → Bool,
      (𝔼 (y : Fin m → Bool), ind ((xor (!(y ⟨t, ht⟩)) (D (hyb S f t x y))) == nwGen S f x ⟨t, ht⟩))
        = 1 / 2 + ((𝔼 (y : Fin m → Bool), ind (D (hyb S f (t + 1) x y)))
            - 𝔼 (y : Fin m → Bool), ind (D (hyb S f t x y))) := by
    intro x
    obtain ⟨b, hb⟩ : ∃ b, nwGen S f x ⟨t, ht⟩ = b := ⟨_, rfl⟩
    have hsucc : ∀ y : Fin m → Bool,
        hyb S f (t + 1) x y = hyb S f t x (Function.update y ⟨t, ht⟩ b) := by
      intro y; rw [hyb_succ S f ht x y, hb]
    simp only [hsucc, hb]
    rw [expect_update_bool ⟨t, ht⟩
        (fun y => ind ((xor (!(y ⟨t, ht⟩)) (D (hyb S f t x y))) == b)),
      expect_update_bool ⟨t, ht⟩ fun y => ind (D (hyb S f t x y))]
    rw [show (1 : ℝ) / 2 = 𝔼 (_y : Fin m → Bool), (1 : ℝ) / 2 from
      (Finset.expect_const univ_nonempty _).symm]
    rw [← Finset.expect_sub_distrib, ← Finset.expect_add_distrib]
    refine Finset.expect_congr rfl fun y _ => ?_
    simp only [Function.update_self]
    cases b <;>
      cases hdt : D (hyb S f t x (Function.update y ⟨t, ht⟩ true)) <;>
      cases hdf : D (hyb S f t x (Function.update y ⟨t, ht⟩ false)) <;>
      norm_num [ind, hdt, hdf]
  rw [pr_prod, hybProb, hybProb, pr_prod, pr_prod]
  simp only []
  rw [Finset.expect_congr rfl fun x _ => key x]
  rw [Finset.expect_add_distrib, Finset.expect_const univ_nonempty, Finset.expect_sub_distrib]

lemma pr_not {α : Type*} [Fintype α] [Nonempty α] (q r : α → Bool) :
    (pr fun a => (!q a) == r a) = 1 - pr fun a => q a == r a := by
  unfold pr
  rw [eq_sub_iff_add_eq, ← Finset.expect_add_distrib]
  rw [show (1 : ℝ) = 𝔼 _a : α, (1 : ℝ) from (Finset.expect_const univ_nonempty 1).symm]
  refine Finset.expect_congr rfl fun a _ => ?_
  cases hq : q a <;> cases hr : r a <;> simp [ind, hq, hr]

/-- Fixing the seed bits outside the `t`-th block and the random bits turns the
next-bit predictor into a genuine Nisan–Wigderson predictor for `f`. -/
lemma glue_predictor {n m ℓ d : ℕ} {S : Fin m → Fin n → Fin ℓ}
    (hSinj : ∀ i, Function.Injective (S i))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      (univ.filter fun k : Fin n => ∃ k', S j k' = S i k).card ≤ d)
    (f : (Fin n → Bool) → Bool) (D : (Fin m → Bool) → Bool) {t : ℕ} (ht : t < m)
    (c : (Fin m → Bool) → Bool) :
    ∃ g : (Fin n → Bool) → Bool, IsNWPredictor d D t g ∧
      (pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
          (xor (c p.2) (D (hyb S f t p.1 p.2)) == nwGen S f p.1 ⟨t, ht⟩))
        ≤ pr fun z => g z == f z := by
  set it : Fin m := ⟨t, ht⟩ with hit
  set σ : Fin n → Fin ℓ := S it with hσdef
  set Φ : (Fin ℓ → Bool) → (Fin m → Bool) → ℝ :=
    fun x y => ind (xor (c y) (D (hyb S f t x y)) == nwGen S f x it) with hΦ
  have hLHS : (pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
          (xor (c p.2) (D (hyb S f t p.1 p.2)) == nwGen S f p.1 it))
      = 𝔼 (x : Fin ℓ → Bool), 𝔼 (y : Fin m → Bool), Φ x y := pr_prod _
  have hswap : (𝔼 (x : Fin ℓ → Bool), 𝔼 (y : Fin m → Bool), Φ x y)
      = 𝔼 (x0 : Fin ℓ → Bool), 𝔼 (y : Fin m → Bool), 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y := by
    rw [expect_glue (hSinj it) fun x => 𝔼 (y : Fin m → Bool), Φ x y]
    rw [Finset.expect_comm]
    refine Finset.expect_congr rfl fun x0 _ => ?_
    exact Finset.expect_comm _ _ _
  obtain ⟨x0, hx0⟩ := exists_ge_expect
    (fun x0 : Fin ℓ → Bool => 𝔼 (y : Fin m → Bool), 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y)
  obtain ⟨y, hy⟩ := exists_ge_expect
    (fun y : Fin m → Bool => 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y)
  refine ⟨fun z => xor (c y) (D (hyb S f t (glue σ z x0) y)), ?_, ?_⟩
  · refine ⟨fun j z => if (j : ℕ) < t then f (fun k => glue σ z x0 (S j k)) else false,
      y, c y, ?_, ?_⟩
    · intro j
      by_cases hj : (j : ℕ) < t
      · refine ⟨univ.filter fun k : Fin n => ∃ k', S j k' = σ k, ?_, ?_⟩
        · refine hdesign it j ?_
          intro hcon
          rw [← hcon] at hj
          exact absurd hj (lt_irrefl t)
        · intro z z' hzz
          simp only [hj, if_true]
          congr 1
          funext k'
          by_cases hmem : ∃ k, σ k = S j k'
          · obtain ⟨k, hk⟩ := hmem
            rw [← hk, glue_apply_mem (hSinj it), glue_apply_mem (hSinj it)]
            refine hzz k ?_
            simp only [mem_filter, mem_univ, true_and]
            exact ⟨k', hk.symm⟩
          · push_neg at hmem
            rw [glue_apply_not_mem _ _ hmem, glue_apply_not_mem _ _ hmem]
      · exact ⟨∅, by simp, by intro z z' _; simp [hj]⟩
    · intro z
      have hh : (hyb S f t (glue σ z x0) y)
          = fun j : Fin m => if (j : ℕ) < t then
              (if (j : ℕ) < t then f (fun k => glue σ z x0 (S j k)) else false) else y j := by
        funext j
        by_cases hj : (j : ℕ) < t <;> simp [hyb, hj, nwGen]
      simp only
      rw [hh]
  · have hkey : (𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y)
        = pr fun z => (xor (c y) (D (hyb S f t (glue σ z x0) y))) == f z := by
      unfold pr
      refine Finset.expect_congr rfl fun z _ => ?_
      simp only [hΦ]
      congr 2
      show nwGen S f (glue σ z x0) it = f z
      simp only [nwGen]
      congr 1
      funext k
      exact glue_apply_mem (hSinj it) z x0 k
    rw [hLHS, hswap]
    calc (𝔼 (x0 : Fin ℓ → Bool), 𝔼 (y : Fin m → Bool), 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y)
        ≤ 𝔼 (y : Fin m → Bool), 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y := hx0
      _ ≤ 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y := hy
      _ = _ := hkey

/-- Combination of the two previous steps: a hybrid gap of `δ` at step `t` yields a
Nisan–Wigderson predictor for `f` with advantage `δ`. -/
lemma exists_predictor {n m ℓ d : ℕ} {S : Fin m → Fin n → Fin ℓ}
    (hSinj : ∀ i, Function.Injective (S i))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      (univ.filter fun k : Fin n => ∃ k', S j k' = S i k).card ≤ d)
    (f : (Fin n → Bool) → Bool) (D : (Fin m → Bool) → Bool) {t : ℕ} (ht : t < m) :
    ∃ g : (Fin n → Bool) → Bool, IsNWPredictor d D t g ∧
      1 / 2 + |hybProb S f D (t + 1) - hybProb S f D t| ≤ pr fun z => g z == f z := by
  have hyao := yao_predictor S f D ht
  rcases le_or_gt 0 (hybProb S f D (t + 1) - hybProb S f D t) with hδ | hδ
  · obtain ⟨g, hg, hle⟩ :=
      glue_predictor hSinj hdesign f D ht fun y : Fin m → Bool => !(y ⟨t, ht⟩)
    refine ⟨g, hg, ?_⟩
    rw [abs_of_nonneg hδ, ← hyao]
    exact hle
  · obtain ⟨g, hg, hle⟩ :=
      glue_predictor hSinj hdesign f D ht fun y : Fin m → Bool => y ⟨t, ht⟩
    refine ⟨g, hg, ?_⟩
    have hrw : (pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
          (xor (p.2 ⟨t, ht⟩) (D (hyb S f t p.1 p.2)) == nwGen S f p.1 ⟨t, ht⟩))
        = 1 - (1 / 2 + (hybProb S f D (t + 1) - hybProb S f D t)) := by
      rw [← hyao, ← pr_not (fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
        xor (!(p.2 ⟨t, ht⟩)) (D (hyb S f t p.1 p.2))) fun p => nwGen S f p.1 ⟨t, ht⟩]
      congr 1
      funext p
      have hxor : ∀ a w : Bool, xor a w = !(xor (!a) w) := by decide
      rw [hxor]
    rw [abs_of_neg hδ]
    calc 1 / 2 + -(hybProb S f D (t + 1) - hybProb S f D t)
        = 1 - (1 / 2 + (hybProb S f D (t + 1) - hybProb S f D t)) := by ring
      _ = _ := hrw.symm
      _ ≤ _ := hle

lemma telescope_bound {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) (eps : ℝ) (hm : 0 < m)
    (h : ∀ t < m, |hybProb S f D (t + 1) - hybProb S f D t| < eps / m) :
    |hybProb S f D m - hybProb S f D 0| < eps := by
  set A : ℕ → ℝ := fun t => hybProb S f D t with hA
  have hsum : A m - A 0 = ∑ t ∈ range m, (A (t + 1) - A t) := (Finset.sum_range_sub A m).symm
  have hne : (range m).Nonempty := nonempty_range_iff.mpr hm.ne'
  calc |A m - A 0| = |∑ t ∈ range m, (A (t + 1) - A t)| := by rw [hsum]
    _ ≤ ∑ t ∈ range m, |A (t + 1) - A t| := Finset.abs_sum_le_sum_abs _ _
    _ < ∑ _t ∈ range m, eps / m :=
        Finset.sum_lt_sum_of_nonempty hne fun t htm => h t (mem_range.mp htm)
    _ = eps := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]
        field_simp

/-! ### Main theorem -/

/-- **The Nisan–Wigderson generator derandomizes from a hard function.**

Let `S` be a combinatorial design: `m` subsets of size `n` of a seed of `ℓ` bits (given as
injections `S i : Fin n → Fin ℓ`) whose pairwise intersections have size at most `d`.
Let `f : (Fin n → Bool) → Bool` and let `D` be any distinguisher on `m` bits.

If `f` cannot be computed with advantage `eps/m` over the trivial guess by *any*
Nisan–Wigderson predictor built out of `D`, `d`-juntas and hard-wired advice bits, then the
Nisan–Wigderson generator `nwGen S f` fools `D` with error `eps`: the acceptance probability
of `D` on a pseudorandom string `nwGen S f x` (uniform seed `x`) differs by less than `eps`
from its acceptance probability on a truly uniform `m`-bit string. -/
theorem nisan_wigderson_prg {n m ℓ d : ℕ} (hm : 0 < m)
    {S : Fin m → Fin n → Fin ℓ} (hSinj : ∀ i, Function.Injective (S i))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      (univ.filter fun k : Fin n => ∃ k', S j k' = S i k).card ≤ d)
    (f : (Fin n → Bool) → Bool) (D : (Fin m → Bool) → Bool) (eps : ℝ)
    (hard : ∀ t : ℕ, ∀ g : (Fin n → Bool) → Bool, IsNWPredictor d D t g →
      (pr fun z => g z == f z) < 1 / 2 + eps / m) :
    |(pr fun x => D (nwGen S f x)) - pr D| < eps := by
  rw [← hybProb_card S f D, ← hybProb_zero S f D]
  refine telescope_bound S f D eps hm ?_
  intro t ht
  obtain ⟨g, hg, hadv⟩ := exists_predictor hSinj hdesign f D ht
  have := hard t g hg
  linarith

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

