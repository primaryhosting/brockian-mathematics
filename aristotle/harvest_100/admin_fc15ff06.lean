import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace CS

open Finset

/-- Real-valued indicator of a boolean: `1` for `true`, `0` for `false`. -/
def bv (b : Bool) : ℝ := if b then 1 else 0

@[simp] lemma bv_true : bv true = 1 := rfl
@[simp] lemma bv_false : bv false = 0 := rfl

/-- `g : {0,1}^l → {0,1}` is an `α`-junta: it depends on at most `α` of its input bits. -/
def IsJunta (α : ℕ) {l : ℕ} (g : (Fin l → Bool) → Bool) : Prop :=
  ∃ T : Finset (Fin l), T.card ≤ α ∧
    ∀ y y' : Fin l → Bool, (∀ t ∈ T, y t = y' t) → g y = g y'

lemma isJunta_const (α : ℕ) {l : ℕ} (b : Bool) : IsJunta α (fun _ : Fin l → Bool => b) :=
  ⟨∅, by simp, fun _ _ _ => rfl⟩

/-- A generic "hybrid argument": if the endpoints of a sequence of `m` steps differ by more
than `ε`, some single step contributes more than `ε / m`. -/
lemma exists_hybrid_gap {m : ℕ} (hm : 0 < m) (p : ℕ → ℝ) (ε : ℝ)
    (h : ε < p m - p 0) : ∃ k, k < m ∧ ε / m < p (k + 1) - p k := by
  by_contra hc
  push_neg at hc
  have hsum : p m - p 0 = ∑ k ∈ range m, (p (k + 1) - p k) := (Finset.sum_range_sub p m).symm
  have hle : ∑ k ∈ range m, (p (k + 1) - p k) ≤ ∑ _k ∈ range m, ε / m :=
    Finset.sum_le_sum (fun k hk => hc k (Finset.mem_range.1 hk))
  rw [Finset.sum_const, card_range, nsmul_eq_mul] at hle
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have : (m : ℝ) * (ε / m) = ε := by field_simp
  rw [this] at hle
  linarith [hsum ▸ hle]

section NW

variable {n l m : ℕ}

/-- The Nisan–Wigderson generator built from a family of index maps `S` and a function `f`:
its `j`-th output bit is `f` applied to the seed `x` restricted along `S j`. -/
def nwGen (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool) (x : Fin n → Bool) :
    Fin m → Bool := fun j => f (fun t => x (S j t))

/-- The `k`-th hybrid: the first `k` output bits come from the generator, the rest are the
"random" bits `r`. -/
def hyb (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool) (k : ℕ)
    (x : Fin n → Bool) (r : Fin m → Bool) : Fin m → Bool :=
  fun j => if (j : ℕ) < k then f (fun t => x (S j t)) else r j

/-- `ov s x y` overwrites the string `x` along `s`, so that its `s v`-th bit becomes `y v`. -/
noncomputable def ov (s : Fin l → Fin n) (x : Fin n → Bool) (y : Fin l → Bool) : Fin n → Bool :=
  fun t => if h : ∃ v, s v = t then y h.choose else x t

lemma ov_apply {l n : ℕ} {s : Fin l → Fin n} (hs : Function.Injective s) (x : Fin n → Bool)
    (y : Fin l → Bool) (v : Fin l) : ov s x y (s v) = y v := by
  have h : ∃ w, s w = s v := ⟨v, rfl⟩
  simp only [ov, dif_pos h]
  congr 1
  exact hs h.choose_spec

lemma ov_ov {l n : ℕ} {s : Fin l → Fin n} (hs : Function.Injective s) (x : Fin n → Bool)
    (y : Fin l → Bool) : ov s (ov s x y) (fun v => x (s v)) = x := by
  funext t
  by_cases h : ∃ v, s v = t
  · obtain ⟨v, rfl⟩ := h
    exact ov_apply hs _ _ v
  · simp only [ov, dif_neg h]

/-- Averaging over the overwritten string is the same as averaging over the original one. -/
lemma sum_ov {l n : ℕ} {s : Fin l → Fin n} (hs : Function.Injective s) (F : (Fin n → Bool) → ℝ) :
    ∑ x : Fin n → Bool, ∑ y : Fin l → Bool, F (ov s x y)
      = 2 ^ l * ∑ x : Fin n → Bool, F x := by
  have hinv : Function.Involutive
      (fun p : (Fin n → Bool) × (Fin l → Bool) => (ov s p.1 p.2, fun v => p.1 (s v))) := by
    rintro ⟨x, y⟩
    have h1 : ov s (ov s x y) (fun v => x (s v)) = x := ov_ov hs x y
    have h2 : (fun v => (ov s x y) (s v)) = y := funext (ov_apply hs x y)
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩
  have key := Equiv.sum_comp (Function.Involutive.toPerm _ hinv)
    (fun p : (Fin n → Bool) × (Fin l → Bool) => F p.1)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at key
  simpa [Finset.mul_sum] using key

lemma flip_involutive {m : ℕ} (i : Fin m) :
    Function.Involutive (fun r : Fin m → Bool => Function.update r i (!(r i))) := by
  intro r
  simp only [Function.update_self, Bool.not_not, Function.update_idem, Function.update_eq_self]

lemma sum_flip {m : ℕ} (i : Fin m) (G : (Fin m → Bool) → ℝ) :
    ∑ r : Fin m → Bool, G (Function.update r i (!(r i))) = ∑ r, G r := by
  simpa using Equiv.sum_comp (Function.Involutive.toPerm _ (flip_involutive i)) G

lemma hyb_eq_update {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (k : ℕ) (i : Fin m) (hi : (i : ℕ) = k) (x : Fin n → Bool) (r : Fin m → Bool) :
    hyb S f k x r = Function.update (hyb S f (k + 1) x r) i (r i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [hyb, hi]
  · have hjk : (j : ℕ) ≠ k := fun h => hj (Fin.ext (h.trans hi.symm))
    rw [Function.update_of_ne hj]
    simp only [hyb]
    by_cases h : (j : ℕ) < k
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

lemma hyb_succ_flip {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (k : ℕ) (i : Fin m) (hi : (i : ℕ) = k) (x : Fin n → Bool) (r : Fin m → Bool) :
    hyb S f (k + 1) x (Function.update r i (!(r i))) = hyb S f (k + 1) x r := by
  funext j
  simp only [hyb]
  by_cases h : (j : ℕ) < k + 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have hj : j ≠ i := fun e => by subst e; omega
    rw [Function.update_of_ne hj]

lemma hyb_apply_self {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (k : ℕ) (i : Fin m) (hi : (i : ℕ) = k) (x : Fin n → Bool) (r : Fin m → Bool) :
    hyb S f (k + 1) x r i = f (fun t => x (S i t)) := by
  simp [hyb, hi]

/-- The success indicator of the next-bit predictor built from the distinguisher `D`
at hybrid `k`: it predicts the `i`-th output bit `f (x ∘ S i)` from the earlier bits. -/
def succTerm {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) (k : ℕ) (i : Fin m) (x : Fin n → Bool) (r : Fin m → Bool) : ℝ :=
  if xor (D (hyb S f k x r)) (!(r i)) = f (fun t => x (S i t)) then 1 else 0

/-- The elementary Boolean identity behind Yao's next-bit predictor. -/
lemma yao_pointwise {m : ℕ} (D : (Fin m → Bool) → Bool) (T : Fin m → Bool) (i : Fin m)
    (b c : Bool) :
    (if xor (D (Function.update T i c)) (!c) = b then (1 : ℝ) else 0)
      + (if xor (D (Function.update T i (!c))) (!(!c)) = b then (1 : ℝ) else 0)
      = 2 * bv (D (Function.update T i b)) - bv (D (Function.update T i c))
        - bv (D (Function.update T i (!c))) + 1 := by
  cases b <;> cases c <;>
    cases hu : D (Function.update T i true) <;> cases hv : D (Function.update T i false) <;>
      norm_num [bv, hu, hv]

/-- Yao's next-bit predictor: the success probability of the predictor built from a
distinguisher between two consecutive hybrids is `1/2` plus the distinguishing advantage. -/
lemma yao_sum {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) (k : ℕ) (i : Fin m) (hi : (i : ℕ) = k) :
    ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, succTerm S f D k i x r
      = (2 : ℝ) ^ n * 2 ^ m / 2
        + (∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f (k + 1) x r)))
        - ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f k x r)) := by
  classical
  simp only [succTerm]
  set su : (Fin n → Bool) → (Fin m → Bool) → ℝ := fun x r =>
    (if xor (D (hyb S f k x r)) (!(r i)) = f (fun t => x (S i t)) then (1 : ℝ) else 0) with hsu
  set L : ℝ := ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, su x r with hL
  set A : ℝ := ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f (k + 1) x r)) with hA
  set B : ℝ := ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f k x r)) with hB
  have key : ∀ (x : Fin n → Bool) (r : Fin m → Bool),
      su x r + su x (Function.update r i (!(r i)))
        = 2 * bv (D (hyb S f (k + 1) x r)) - bv (D (hyb S f k x r))
          - bv (D (hyb S f k x (Function.update r i (!(r i))))) + 1 := by
    intro x r
    have hT : hyb S f (k + 1) x r i = f (fun t => x (S i t)) := hyb_apply_self S f k i hi x r
    have e1 : hyb S f k x r = Function.update (hyb S f (k + 1) x r) i (r i) :=
      hyb_eq_update S f k i hi x r
    have e2 : hyb S f k x (Function.update r i (!(r i)))
        = Function.update (hyb S f (k + 1) x r) i (!(r i)) := by
      rw [hyb_eq_update S f k i hi x (Function.update r i (!(r i))),
        hyb_succ_flip S f k i hi x r, Function.update_self]
    have e3 : Function.update (hyb S f (k + 1) x r) i (f (fun t => x (S i t)))
        = hyb S f (k + 1) x r := by
      rw [← hT, Function.update_eq_self]
    have hp := yao_pointwise D (hyb S f (k + 1) x r) i (f (fun t => x (S i t))) (r i)
    rw [e3] at hp
    simp only [hsu]
    rw [e1, e2, Function.update_self]
    exact hp
  have hflip1 : ∀ x : Fin n → Bool,
      ∑ r : Fin m → Bool, su x (Function.update r i (!(r i))) = ∑ r : Fin m → Bool, su x r :=
    fun x => sum_flip i (fun r => su x r)
  have hflip2 : ∀ x : Fin n → Bool,
      ∑ r : Fin m → Bool, bv (D (hyb S f k x (Function.update r i (!(r i)))))
        = ∑ r : Fin m → Bool, bv (D (hyb S f k x r)) :=
    fun x => sum_flip i (fun r => bv (D (hyb S f k x r)))
  have step1 : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool,
      (su x r + su x (Function.update r i (!(r i))))
      = ∑ x : Fin n → Bool, ∑ r : Fin m → Bool,
        (2 * bv (D (hyb S f (k + 1) x r)) - bv (D (hyb S f k x r))
          - bv (D (hyb S f k x (Function.update r i (!(r i))))) + 1) :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun r _ => key x r
  have step2 : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool,
      (su x r + su x (Function.update r i (!(r i)))) = 2 * L := by
    rw [hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_add_distrib, hflip1 x, two_mul]
  have step3 : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool,
      (2 * bv (D (hyb S f (k + 1) x r)) - bv (D (hyb S f k x r))
        - bv (D (hyb S f k x (Function.update r i (!(r i))))) + 1)
      = 2 * A - 2 * B + 2 ^ n * 2 ^ m := by
    have : ∀ x : Fin n → Bool, ∑ r : Fin m → Bool,
        (2 * bv (D (hyb S f (k + 1) x r)) - bv (D (hyb S f k x r))
          - bv (D (hyb S f k x (Function.update r i (!(r i))))) + 1)
        = 2 * (∑ r : Fin m → Bool, bv (D (hyb S f (k + 1) x r)))
          - 2 * (∑ r : Fin m → Bool, bv (D (hyb S f k x r))) + 2 ^ m := by
      intro x
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        hflip2 x, ← Finset.mul_sum]
      simp [two_mul]
      ring
    rw [Finset.sum_congr rfl fun x _ => this x]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hA, hB]
    simp [Finset.sum_const]
  rw [step2] at step1
  rw [step3] at step1
  linarith

/-- **Nisan–Wigderson reconstruction.**  If a distinguisher `D` tells the output of the
Nisan–Wigderson generator built from `f` and a combinatorial design `S` apart from uniform
with advantage more than `ε`, then `f` is computed on more than a `1/2 + ε/m` fraction of
its inputs by `D` composed with `α`-juntas (up to a fixed output flip `c`).  Here the design
condition is that any two distinct index sets `S i`, `S j` overlap in at most `α` positions. -/
theorem nisan_wigderson_reconstruction {n l m α : ℕ} (hm : 0 < m)
    (S : Fin m → Fin l → Fin n) (hinj : ∀ i, Function.Injective (S i))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      ((Finset.univ.image (S i)) ∩ (Finset.univ.image (S j))).card ≤ α)
    (f : (Fin l → Bool) → Bool) (D : (Fin m → Bool) → Bool) (ε : ℝ)
    (hdist : ε < (∑ x : Fin n → Bool, bv (D (nwGen S f x))) / 2 ^ n
              - (∑ z : Fin m → Bool, bv (D z)) / 2 ^ m) :
    ∃ (g : Fin m → (Fin l → Bool) → Bool) (c : Bool),
      (∀ j, IsJunta α (g j)) ∧
      (1 : ℝ) / 2 + ε / m
        ≤ ((Finset.univ.filter
            (fun y : Fin l → Bool => xor (D (fun j => g j y)) c = f y)).card : ℝ) / 2 ^ l := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hM : (0 : ℝ) < 2 ^ m := by positivity
  have hL : (0 : ℝ) < 2 ^ l := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- the endpoints of the hybrid sequence
  have hPm : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f m x r))
      = 2 ^ m * ∑ x : Fin n → Bool, bv (D (nwGen S f x)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h : ∀ r : Fin m → Bool, hyb S f m x r = nwGen S f x := by
      intro r; funext j; simp [hyb, nwGen, j.isLt]
    simp [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP0 : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f 0 x r))
      = 2 ^ n * ∑ z : Fin m → Bool, bv (D z) := by
    have h : ∀ (x r : _), hyb S f 0 x (r : Fin m → Bool) = r := by
      intro x r; funext j; simp [hyb]
    simp [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the hybrid argument
  obtain ⟨k, hk, hgap⟩ :=
    exists_hybrid_gap hm (fun k => ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f k x r)))
      (ε * (2 ^ n * 2 ^ m)) (by
        simp only [hPm, hP0]
        have h1 : (2 ^ n * 2 ^ m : ℝ) * ε
            < (2 ^ n * 2 ^ m : ℝ) * ((∑ x : Fin n → Bool, bv (D (nwGen S f x))) / 2 ^ n
                - (∑ z : Fin m → Bool, bv (D z)) / 2 ^ m) :=
          mul_lt_mul_of_pos_left hdist (by positivity)
        have h2 : (2 ^ n * 2 ^ m : ℝ) * ((∑ x : Fin n → Bool, bv (D (nwGen S f x))) / 2 ^ n
                - (∑ z : Fin m → Bool, bv (D z)) / 2 ^ m)
            = 2 ^ m * (∑ x : Fin n → Bool, bv (D (nwGen S f x)))
              - 2 ^ n * ∑ z : Fin m → Bool, bv (D z) := by
          field_simp
        rw [h2] at h1
        linarith)
  set i : Fin m := ⟨k, hk⟩ with hidef
  have hik : (i : ℕ) = k := rfl
  -- Yao's next-bit predictor
  have hyao := yao_sum S f D k i hik
  have hbig : (2 : ℝ) ^ n * 2 ^ m * (1 / 2 + ε / m)
      < ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, succTerm S f D k i x r := by
    rw [hyao]
    have : (2 : ℝ) ^ n * 2 ^ m * (1 / 2 + ε / m)
        = 2 ^ n * 2 ^ m / 2 + ε * (2 ^ n * 2 ^ m) / m := by ring
    rw [this]
    linarith
  -- fix the seed outside the `i`-th index set, and the random bits
  have hov : ∀ r : Fin m → Bool,
      ∑ x : Fin n → Bool, ∑ y : Fin l → Bool, succTerm S f D k i (ov (S i) x y) r
        = 2 ^ l * ∑ x : Fin n → Bool, succTerm S f D k i x r :=
    fun r => sum_ov (hinj i) (fun x => succTerm S f D k i x r)
  have hconst : ∑ _r : Fin m → Bool, ∑ _x : Fin n → Bool, ((2 : ℝ) ^ l * (1 / 2 + ε / m))
      = 2 ^ n * 2 ^ m * (2 ^ l * (1 / 2 + ε / m)) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have htot : ∑ _r : Fin m → Bool, ∑ _x : Fin n → Bool, ((2 : ℝ) ^ l * (1 / 2 + ε / m))
      < ∑ r : Fin m → Bool, ∑ x : Fin n → Bool,
          ∑ y : Fin l → Bool, succTerm S f D k i (ov (S i) x y) r := by
    rw [hconst]
    have h1 : ∑ r : Fin m → Bool, ∑ x : Fin n → Bool,
        ∑ y : Fin l → Bool, succTerm S f D k i (ov (S i) x y) r
        = 2 ^ l * ∑ r : Fin m → Bool, ∑ x : Fin n → Bool, succTerm S f D k i x r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => hov r
    rw [h1, Finset.sum_comm,
      show (2 : ℝ) ^ n * 2 ^ m * (2 ^ l * (1 / 2 + ε / m))
        = 2 ^ l * (2 ^ n * 2 ^ m * (1 / 2 + ε / m)) from by ring]
    exact mul_lt_mul_of_pos_left hbig hL
  obtain ⟨r₀, -, h1⟩ := Finset.exists_lt_of_sum_lt htot
  obtain ⟨x₀, -, h2⟩ := Finset.exists_lt_of_sum_lt h1
  -- the reconstructed predictor
  refine ⟨fun j y => if (j : ℕ) < k then f (fun t => ov (S i) x₀ y (S j t)) else r₀ j,
    !(r₀ i), ?_, ?_⟩
  · -- each coordinate function is an `α`-junta
    intro j
    by_cases hj : (j : ℕ) < k
    · refine ⟨Finset.univ.filter (fun v : Fin l => ∃ u, S j u = S i v), ?_, ?_⟩
      · have hmaps : ∀ v ∈ Finset.univ.filter (fun v : Fin l => ∃ u, S j u = S i v),
            S i v ∈ (Finset.univ.image (S i)) ∩ (Finset.univ.image (S j)) := by
          intro v hv
          rw [Finset.mem_filter] at hv
          obtain ⟨u, hu⟩ := hv.2
          exact Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩,
            Finset.mem_image.2 ⟨u, Finset.mem_univ u, hu⟩⟩
        refine le_trans (Finset.card_le_card_of_injOn (S i)
          (fun v hv => Finset.mem_coe.2 (hmaps v (Finset.mem_coe.1 hv)))
          (fun a _ b _ h => hinj i h)) (hdesign i j ?_)
        intro h
        have hji : (j : ℕ) = k := by rw [← h]; exact hik
        omega
      · intro y y' hyy
        simp only [if_pos hj]
        congr 1
        funext t
        by_cases hv : ∃ v, S i v = S j t
        · obtain ⟨v, hv'⟩ := hv
          rw [← hv', ov_apply (hinj i), ov_apply (hinj i)]
          exact hyy v (Finset.mem_filter.2 ⟨Finset.mem_univ v, ⟨t, hv'.symm⟩⟩)
        · simp only [ov, dif_neg hv]
    · exact ⟨∅, by simp, fun y y' _ => by simp only [if_neg hj]⟩
  · -- the predictor agrees with `f` often
    have hcount : ∑ y : Fin l → Bool, succTerm S f D k i (ov (S i) x₀ y) r₀
        = ((Finset.univ.filter (fun y : Fin l → Bool =>
            xor (D (fun j => if (j : ℕ) < k then f (fun t => ov (S i) x₀ y (S j t)) else r₀ j))
              (!(r₀ i)) = f y)).card : ℝ) := by
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl fun y _ => ?_
      have e1 : hyb S f k (ov (S i) x₀ y) r₀
          = fun j => if (j : ℕ) < k then f (fun t => ov (S i) x₀ y (S j t)) else r₀ j := by
        funext j
        rfl
      have e2 : f (fun t => ov (S i) x₀ y (S i t)) = f y := by
        congr 1
        funext t
        exact ov_apply (hinj i) _ _ t
      simp only [succTerm, e1, e2]
    rw [hcount] at h2
    rw [le_div_iff₀ hL]
    linarith [h2]

end NW

end CS

