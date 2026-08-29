import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
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

namespace CS

open Finset

variable {n m : ℕ}

/-- The real value of a boolean: `1` for `true`, `0` for `false`. -/
def bval (b : Bool) : ℝ := if b then 1 else 0

/-- The average of a real valued function over the uniform distribution on a finite type. -/
noncomputable def unifAvg {α : Type*} [Fintype α] (g : α → ℝ) : ℝ :=
  (∑ a, g a) / (Fintype.card α : ℝ)

/-- `maskMerge S x z` agrees with `x` on `S` and with `z` off `S`. -/
def maskMerge (S : Finset (Fin n)) (x z : Fin n → Bool) : Fin n → Bool :=
  fun j => if j ∈ S then x j else z j

/-- The `k`-th hybrid string: the first `k` bits come from the generator, the rest from `u`. -/
def hyb (f : Fin m → (Fin n → Bool) → Bool) (k : ℕ)
    (x : Fin n → Bool) (u : Fin m → Bool) : Fin m → Bool :=
  fun j => if (j : ℕ) < k then f j x else u j

/-- The Nisan–Wigderson generator associated to the family `f` of (local) hard functions. -/
def nwGen (f : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) : Fin m → Bool :=
  fun i => f i x

/-- The string fed to the test by the Nisan–Wigderson predictor for position `i`. -/
def nwStr (f : Fin m → (Fin n → Bool) → Bool) (i : Fin m) (x : Fin n → Bool)
    (tail : Fin m → Bool) (v : Bool) : Fin m → Bool :=
  fun j => if (j : ℕ) < (i : ℕ) then f j x else if j = i then v else tail j

/-- The Nisan–Wigderson predictor for position `i`, built from the test `T`, the guess `ui`,
the fixed suffix `tail` and the fixed seed bits `z` outside the set `S`. -/
def nwPred (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool) (i : Fin m)
    (S : Finset (Fin n)) (ui : Bool) (tail : Fin m → Bool) (z : Fin n → Bool) :
    (Fin n → Bool) → Bool :=
  fun x => if T (nwStr f i (maskMerge S x z) tail ui) then ui else !ui

/-- The acceptance probability of the test `T` on the `k`-th hybrid distribution. -/
noncomputable def hybAvg (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool)
    (k : ℕ) : ℝ :=
  (∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f k x u))) / ((2 : ℝ) ^ n * 2 ^ m)

/-! ### Basic counting lemmas -/

lemma card_seed (N : ℕ) : (Fintype.card (Fin N → Bool) : ℝ) = 2 ^ N := by
  simp

lemma exists_ge_unifAvg {α : Type*} [Fintype α] [Nonempty α] (g : α → ℝ) :
    ∃ a, unifAvg g ≤ g a := by
  have hcard : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ _a : α, unifAvg g ≤ ∑ a, g a := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unifAvg,
      mul_div_cancel₀ _ (ne_of_gt hcard)]
  obtain ⟨a, -, ha⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨a, ha⟩

lemma sum_maskMerge (S : Finset (Fin n)) (g : (Fin n → Bool) → ℝ) :
    ∑ x : Fin n → Bool, ∑ z : Fin n → Bool, g (maskMerge S x z)
      = 2 ^ n * ∑ x : Fin n → Bool, g x := by
  have hinv : Function.Involutive (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      (maskMerge S p.1 p.2, maskMerge S p.2 p.1)) := by
    intro p
    ext1 <;> · funext j; by_cases h : j ∈ S <;> simp [maskMerge, h]
  have h1 : ∑ p : (Fin n → Bool) × (Fin n → Bool), g (maskMerge S p.1 p.2)
      = ∑ p : (Fin n → Bool) × (Fin n → Bool), g p.1 :=
    Fintype.sum_equiv (hinv.toPerm _) _ _ (fun _ => rfl)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h1
  rw [h1]
  simp [Finset.mul_sum, mul_comm]

lemma sum_update_bool (i : Fin m) (g : (Fin m → Bool) → ℝ) :
    ∑ tail : Fin m → Bool, ∑ v : Bool, g (Function.update tail i v)
      = 2 * ∑ u : Fin m → Bool, g u := by
  have hinv : Function.Involutive (fun p : (Fin m → Bool) × Bool =>
      (Function.update p.1 i p.2, p.1 i)) := by
    intro p
    ext1
    · funext j; by_cases h : j = i <;> simp [Function.update_apply, h]
    · simp
  have h1 : ∑ p : (Fin m → Bool) × Bool, g (Function.update p.1 i p.2)
      = ∑ p : (Fin m → Bool) × Bool, g p.1 :=
    Fintype.sum_equiv (hinv.toPerm _) _ _ (fun _ => rfl)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h1
  rw [h1]
  simp [Finset.mul_sum, mul_comm]

/-! ### Identities about the hybrid strings -/

lemma nwStr_eq_hyb (f : Fin m → (Fin n → Bool) → Bool) (i : Fin m) (x : Fin n → Bool)
    (tail : Fin m → Bool) (v : Bool) :
    nwStr f i x tail v = hyb f (i : ℕ) x (Function.update tail i v) := by
  funext j
  simp [nwStr, hyb, Function.update_apply]

lemma nwStr_eq_hyb_succ (f : Fin m → (Fin n → Bool) → Bool) (i : Fin m) (x : Fin n → Bool)
    (tail : Fin m → Bool) :
    nwStr f i x tail (f i x) = hyb f ((i : ℕ) + 1) x tail := by
  funext j
  by_cases h : (j : ℕ) < (i : ℕ)
  · simp [nwStr, hyb, h, Nat.lt_succ_of_lt h]
  · by_cases h2 : j = i
    · subst h2; simp [nwStr, hyb]
    · have h3 : ¬ ((j : ℕ) < (i : ℕ) + 1) := by
        have : (j : ℕ) ≠ (i : ℕ) := fun hc => h2 (Fin.ext hc)
        omega
      simp [nwStr, hyb, h, h2, h3]

/-! ### The one-bit prediction identity -/

lemma bool_pred_sum (g : Bool → Bool) (c : Bool) :
    ∑ ui : Bool, bval ((if g ui then ui else !ui) == c)
      = 1 + 2 * bval (g c) - ∑ v : Bool, bval (g v) := by
  rw [Fintype.sum_bool, Fintype.sum_bool]
  cases c <;> cases hgt : g true <;> cases hgf : g false <;> simp [bval, hgt, hgf] <;> norm_num

/-! ### The main averaging identity -/

lemma nwPred_sum (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool)
    (S : Finset (Fin n)) (i : Fin m)
    (hf : ∀ x y : Fin n → Bool, (∀ j ∈ S, x j = y j) → f i x = f i y) :
    (∑ ui : Bool, ∑ tail : Fin m → Bool, ∑ z : Fin n → Bool, ∑ x : Fin n → Bool,
        bval (nwPred f T i S ui tail z x == f i x))
      = 2 ^ n * ((2 : ℝ) ^ m * 2 ^ n
          + 2 * (∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f ((i : ℕ) + 1) x u)))
          - 2 * (∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f (i : ℕ) x u)))) := by
  have hmask : ∀ (ui : Bool) (tail : Fin m → Bool) (z x : Fin n → Bool),
      bval (nwPred f T i S ui tail z x == f i x)
        = (fun x' : Fin n → Bool =>
            bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x')) (maskMerge S x z) := by
    intro ui tail z x
    have h1 : f i x = f i (maskMerge S x z) := hf _ _ (fun j hj => by simp [maskMerge, hj])
    simp only [nwPred]
    rw [h1]
  have stepA : ∀ (ui : Bool) (tail : Fin m → Bool),
      (∑ z : Fin n → Bool, ∑ x : Fin n → Bool, bval (nwPred f T i S ui tail z x == f i x))
        = 2 ^ n * ∑ x' : Fin n → Bool,
            bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x') := by
    intro ui tail
    rw [Finset.sum_comm]
    simp only [hmask]
    exact sum_maskMerge S (fun x' : Fin n → Bool =>
      bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x'))
  have stepB : ∀ (tail : Fin m → Bool) (x' : Fin n → Bool),
      (∑ ui : Bool, bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x'))
        = 1 + 2 * bval (T (hyb f ((i : ℕ) + 1) x' tail))
            - ∑ v : Bool, bval (T (hyb f (i : ℕ) x' (Function.update tail i v))) := by
    intro tail x'
    have h := bool_pred_sum (fun v => T (nwStr f i x' tail v)) (f i x')
    have h2 : (∑ v : Bool, bval (T (nwStr f i x' tail v)))
        = ∑ v : Bool, bval (T (hyb f (i : ℕ) x' (Function.update tail i v))) :=
      Finset.sum_congr rfl (fun v _ => by rw [nwStr_eq_hyb])
    rw [nwStr_eq_hyb_succ, h2] at h
    exact h
  have stepC : ∀ tail : Fin m → Bool,
      (∑ ui : Bool, ∑ x' : Fin n → Bool,
          bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x'))
        = ∑ x' : Fin n → Bool, (1 + 2 * bval (T (hyb f ((i : ℕ) + 1) x' tail))
            - ∑ v : Bool, bval (T (hyb f (i : ℕ) x' (Function.update tail i v)))) := by
    intro tail
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x' _ => stepB tail x')
  have expand : ∀ tail : Fin m → Bool,
      (∑ x' : Fin n → Bool, (1 + 2 * bval (T (hyb f ((i : ℕ) + 1) x' tail))
          - ∑ v : Bool, bval (T (hyb f (i : ℕ) x' (Function.update tail i v)))))
        = 2 ^ n + 2 * (∑ x' : Fin n → Bool, bval (T (hyb f ((i : ℕ) + 1) x' tail)))
            - ∑ x' : Fin n → Bool, ∑ v : Bool,
                bval (T (hyb f (i : ℕ) x' (Function.update tail i v))) := by
    intro tail
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have h1 : (∑ ui : Bool, ∑ tail : Fin m → Bool, ∑ z : Fin n → Bool, ∑ x : Fin n → Bool,
      bval (nwPred f T i S ui tail z x == f i x))
      = ∑ ui : Bool, ∑ tail : Fin m → Bool, 2 ^ n * ∑ x' : Fin n → Bool,
          bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x') :=
    Finset.sum_congr rfl (fun ui _ => Finset.sum_congr rfl (fun tail _ => stepA ui tail))
  rw [h1, Finset.sum_comm]
  simp only [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun tail _ => stepC tail),
    Finset.sum_congr rfl (fun tail _ => expand tail),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hswap : (∑ tail : Fin m → Bool, ∑ x' : Fin n → Bool,
      bval (T (hyb f ((i : ℕ) + 1) x' tail)))
      = ∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f ((i : ℕ) + 1) x u)) :=
    Finset.sum_comm
  have hswap2 : (∑ tail : Fin m → Bool, ∑ x' : Fin n → Bool, ∑ v : Bool,
      bval (T (hyb f (i : ℕ) x' (Function.update tail i v))))
      = 2 * ∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f (i : ℕ) x u)) := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x' _ => sum_update_bool i (fun u => bval (T (hyb f (i : ℕ) x' u))))
  rw [hswap, hswap2]
  simp

lemma nwPred_avg (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool)
    (S : Finset (Fin n)) (i : Fin m)
    (hf : ∀ x y : Fin n → Bool, (∀ j ∈ S, x j = y j) → f i x = f i y) :
    unifAvg (fun a : Bool × (Fin m → Bool) × (Fin n → Bool) =>
        unifAvg (fun x => bval (nwPred f T i S a.1 a.2.1 a.2.2 x == f i x)))
      = 1 / 2 + (hybAvg f T ((i : ℕ) + 1) - hybAvg f T (i : ℕ)) := by
  have hsum := nwPred_sum f T S i hf
  simp only [unifAvg, Fintype.sum_prod_type, ← Finset.sum_div]
  rw [hsum]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hybAvg]
  have h2n : ((2:ℝ) ^ n) ≠ 0 := by positivity
  have h2m : ((2:ℝ) ^ m) ≠ 0 := by positivity
  field_simp
  ring

lemma exists_nwPred (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool)
    (S : Finset (Fin n)) (i : Fin m)
    (hf : ∀ x y : Fin n → Bool, (∀ j ∈ S, x j = y j) → f i x = f i y) :
    ∃ (ui : Bool) (tail : Fin m → Bool) (z : Fin n → Bool),
      1 / 2 + (hybAvg f T ((i : ℕ) + 1) - hybAvg f T (i : ℕ))
        ≤ unifAvg (fun x => bval (nwPred f T i S ui tail z x == f i x)) := by
  obtain ⟨a, ha⟩ := exists_ge_unifAvg (fun a : Bool × (Fin m → Bool) × (Fin n → Bool) =>
    unifAvg (fun x => bval (nwPred f T i S a.1 a.2.1 a.2.2 x == f i x)))
  rw [nwPred_avg f T S i hf] at ha
  exact ⟨a.1, a.2.1, a.2.2, ha⟩

/-! ### Locality of the predictor -/

lemma nwPred_local (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool) (i : Fin m)
    (S : Finset (Fin n)) (ui : Bool) (tail : Fin m → Bool) (z : Fin n → Bool)
    (x y : Fin n → Bool) (h : ∀ j ∈ S, x j = y j) :
    nwPred f T i S ui tail z x = nwPred f T i S ui tail z y := by
  have : maskMerge S x z = maskMerge S y z := by
    funext j
    by_cases hj : j ∈ S
    · simp [maskMerge, hj, h j hj]
    · simp [maskMerge, hj]
  simp [nwPred, this]

/-! ### Endpoints of the hybrid sequence -/

lemma hybAvg_top (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool) :
    hybAvg f T m = unifAvg (fun x : Fin n → Bool => bval (T (nwGen f x))) := by
  have h : ∀ (x : Fin n → Bool) (u : Fin m → Bool), hyb f m x u = nwGen f x := by
    intro x u; funext j; simp [hyb, nwGen, j.isLt]
  simp only [hybAvg, unifAvg, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, ← Finset.mul_sum]
  rw [mul_comm ((2:ℝ)^n) ((2:ℝ)^m), mul_div_mul_left]
  positivity

lemma hybAvg_zero (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool) :
    hybAvg f T 0 = unifAvg (fun u : Fin m → Bool => bval (T u)) := by
  have h : ∀ (x : Fin n → Bool) (u : Fin m → Bool), hyb f 0 x u = u := by
    intro x u; funext j; simp [hyb]
  simp only [hybAvg, unifAvg, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [mul_div_mul_left]
  positivity

lemma hybAvg_not (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool) (k : ℕ) :
    hybAvg f (fun w => !T w) k = 1 - hybAvg f T k := by
  have h : ∀ b : Bool, bval (!b) = 1 - bval b := by intro b; cases b <;> simp [bval]
  simp only [hybAvg, h]
  rw [eq_sub_iff_add_eq, ← add_div, ← Finset.sum_add_distrib]
  have key : ∀ x : Fin n → Bool,
      (∑ u : Fin m → Bool, (1 - bval (T (hyb f k x u))))
        + ∑ u : Fin m → Bool, bval (T (hyb f k x u)) = 2 ^ m := by
    intro x
    rw [Finset.sum_sub_distrib]
    simp
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  simp

/-! ### A large gap in the hybrid sequence -/

lemma exists_gap (d : ℕ → ℝ) (M : ℕ) (hM : 0 < M) (ε : ℝ)
    (hε : ε ≤ |∑ k ∈ Finset.range M, d k|) : ∃ k < M, ε / M ≤ |d k| := by
  by_contra hcon
  push_neg at hcon
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have h1 : |∑ k ∈ Finset.range M, d k| ≤ ∑ k ∈ Finset.range M, |d k| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ k ∈ Finset.range M, |d k| < ∑ _k ∈ Finset.range M, ε / M := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hM.ne')
    intro k hk
    exact hcon k (Finset.mem_range.mp hk)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_div_cancel₀ _ (ne_of_gt hMR)] at h2
  linarith

/-!
### The Nisan–Wigderson theorem

`f i` is a family of functions, each depending only on the seed bits in the set `S i`
(in the Nisan–Wigderson construction the `S i` form a combinatorial design, and `f i` is a hard
function evaluated on the corresponding subset of seed bits).  `nwGen f` is the associated
generator.  The theorem below is the "hardness from distinguishing" core of the
Nisan–Wigderson argument: if some test `T` distinguishes the output of the generator from the
uniform distribution with advantage `ε`, then, for some index `i`, the Nisan–Wigderson predictor
built from `T` computes `f i` correctly with probability at least `1/2 + ε/m`; moreover this
predictor reads only the seed bits in `S i`.  In other words, the generator can only be broken
if the hard function is not hard.
-/
theorem nisan_wigderson_prg {n m : ℕ} (hm : 0 < m)
    (S : Fin m → Finset (Fin n)) (f : Fin m → (Fin n → Bool) → Bool)
    (hf : ∀ (i : Fin m) (x y : Fin n → Bool), (∀ j ∈ S i, x j = y j) → f i x = f i y)
    (T : (Fin m → Bool) → Bool) (ε : ℝ)
    (hε : ε ≤ |unifAvg (fun x : Fin n → Bool => bval (T (nwGen f x)))
                - unifAvg (fun u : Fin m → Bool => bval (T u))|) :
    ∃ (i : Fin m) (P : (Fin n → Bool) → Bool),
      (∃ (b ui : Bool) (tail : Fin m → Bool) (z : Fin n → Bool),
          P = nwPred f (fun w => xor b (T w)) i (S i) ui tail z) ∧
      (∀ x y : Fin n → Bool, (∀ j ∈ S i, x j = y j) → P x = P y) ∧
      1 / 2 + ε / m ≤ unifAvg (fun x => bval (P x == f i x)) := by
  have htel : ∑ k ∈ Finset.range m, (hybAvg f T (k + 1) - hybAvg f T k)
      = hybAvg f T m - hybAvg f T 0 := Finset.sum_range_sub (fun k => hybAvg f T k) m
  have hεs : ε ≤ |∑ k ∈ Finset.range m, (hybAvg f T (k + 1) - hybAvg f T k)| := by
    rw [htel, hybAvg_top, hybAvg_zero]; exact hε
  obtain ⟨k, hk, hkd⟩ := exists_gap (fun k => hybAvg f T (k + 1) - hybAvg f T k) m hm ε hεs
  refine ⟨⟨k, hk⟩, ?_⟩
  rcases abs_cases (hybAvg f T (k + 1) - hybAvg f T k) with ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨ui, tail, z, hP⟩ := exists_nwPred f T (S ⟨k, hk⟩) ⟨k, hk⟩ (hf ⟨k, hk⟩)
    have hT0 : (fun w => xor false (T w)) = T := by funext w; simp
    refine ⟨nwPred f T ⟨k, hk⟩ (S ⟨k, hk⟩) ui tail z, ⟨false, ui, tail, z, by rw [hT0]⟩,
      fun x y hxy => nwPred_local f T ⟨k, hk⟩ (S ⟨k, hk⟩) ui tail z x y hxy, ?_⟩
    refine le_trans ?_ hP
    have : (↑(⟨k, hk⟩ : Fin m) : ℕ) = k := rfl
    rw [this]
    linarith [hkd, habs]
  · obtain ⟨ui, tail, z, hP⟩ :=
      exists_nwPred f (fun w => !T w) (S ⟨k, hk⟩) ⟨k, hk⟩ (hf ⟨k, hk⟩)
    have hT1 : (fun w => xor true (T w)) = (fun w => !T w) := by funext w; simp
    refine ⟨nwPred f (fun w => !T w) ⟨k, hk⟩ (S ⟨k, hk⟩) ui tail z,
      ⟨true, ui, tail, z, by rw [hT1]⟩,
      fun x y hxy => nwPred_local f _ ⟨k, hk⟩ (S ⟨k, hk⟩) ui tail z x y hxy, ?_⟩
    refine le_trans ?_ hP
    have hval : (↑(⟨k, hk⟩ : Fin m) : ℕ) = k := rfl
    rw [hval, hybAvg_not, hybAvg_not]
    linarith [hkd, habs]

end CS

