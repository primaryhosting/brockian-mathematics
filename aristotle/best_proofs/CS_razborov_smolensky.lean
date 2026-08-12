import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/

theorem list_sum_map {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

theorem list_any_iff {α : Type*} (l : List α) (f : α → Bool) :
    (l.map f).any id = true ↔ ∃ i : Fin l.length, f (l.get i) = true := by
  simp [List.any_eq_true, List.mem_iff_get]

theorem list_all_iff {α : Type*} (l : List α) (f : α → Bool) :
    (l.map f).all id = true ↔ ∀ i : Fin l.length, f (l.get i) = true := by
  simp [List.all_eq_true, List.mem_iff_get]

theorem count_true_eq_sum (l : List Bool) :
    l.count true = (l.map (fun b => if b = true then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a
    · simp [ih]
    · simp [ih]; omega

theorem list_count_map {α : Type*} (l : List α) (f : α → Bool) :
    (l.map f).count true = ∑ i : Fin l.length, (if f (l.get i) = true then 1 else 0) := by
  rw [count_true_eq_sum, List.map_map, list_sum_map]
  simp

/-! ### Fermat's little theorem in characteristic `q` -/

theorem natCast_pow_q (F : Type*) [Field F] (q : ℕ) [hq : Fact q.Prime] [CharP F q] (k : ℕ) :
    ((k : F)) ^ (q - 1) = if q ∣ k then 0 else 1 := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have hmap : ((k : F)) = (ZMod.castHom (dvd_refl q) F) (k : ZMod q) := by simp
  split
  · rename_i h
    have h0 : (k : F) = 0 := by
      rw [hmap, (ZMod.natCast_eq_zero_iff k q).2 h, map_zero]
    rw [h0]
    exact zero_pow (by have := hq.out.two_le; omega)
  · rename_i h
    have hne : ((k : ZMod q)) ≠ 0 := fun hc => h ((ZMod.natCast_eq_zero_iff k q).1 hc)
    rw [hmap, ← map_pow, ZMod.pow_card_sub_one_eq_one hne, map_one]

/-! ### At most half of all subsets have weight divisible by `q` -/

/-- If some coordinate `i₀` carries weight, then at most half of all subsets of `Fin m` have
a weight divisible by `q`. -/
theorem card_good_subsets (q m : ℕ) (hq : 2 ≤ q) (z : Fin m → Bool) (i₀ : Fin m)
    (hz : z i₀ = true) :
    2 * #(univ.filter (fun S : Finset (Fin m) =>
      (#(S.filter (fun i => z i = true))) % q = 0)) ≤ 2 ^ m := by
  classical
  set c : Finset (Fin m) → ℕ := fun S => #(S.filter (fun i => z i = true)) with hc
  set G := univ.filter (fun S : Finset (Fin m) => c S % q = 0) with hG
  set f : Finset (Fin m) → Finset (Fin m) := fun S => if i₀ ∈ S then S.erase i₀ else insert i₀ S
    with hf
  have hstep : ∀ S, (i₀ ∈ S → c (f S) + 1 = c S) ∧ (i₀ ∉ S → c (f S) = c S + 1) := by
    intro S
    constructor
    · intro h
      simp only [hf, if_pos h, hc]
      rw [Finset.filter_erase, Finset.card_erase_of_mem (by simp [h, hz])]
      have : 1 ≤ #(S.filter (fun i => z i = true)) :=
        Finset.card_pos.2 ⟨i₀, by simp [h, hz]⟩
      omega
    · intro h
      simp only [hf, if_neg h, hc]
      rw [Finset.filter_insert, if_pos hz, Finset.card_insert_of_notMem (by simp [h])]
  have hinv : ∀ S, f (f S) = S := by
    intro S
    by_cases h : i₀ ∈ S
    · simp only [hf, if_pos h]
      rw [if_neg (by simp)]
      exact Finset.insert_erase h
    · simp only [hf, if_neg h]
      rw [if_pos (by simp)]
      exact Finset.erase_insert h
  have hinj : Function.Injective f := Function.LeftInverse.injective hinv
  have hmaps : ∀ S ∈ G, f S ∈ univ \ G := by
    intro S hS
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hG, Finset.mem_filter]
    intro hbad
    have hd1 : q ∣ c S := Nat.dvd_of_mod_eq_zero hS
    have hd2 : q ∣ c (f S) := Nat.dvd_of_mod_eq_zero hbad
    have hone : q ∣ 1 := by
      by_cases h : i₀ ∈ S
      · have he := (hstep S).1 h
        exact (Nat.dvd_add_iff_right hd2).mpr (by rwa [he])
      · have he := (hstep S).2 h
        exact (Nat.dvd_add_iff_right hd1).mpr (by rwa [he] at hd2)
    have := Nat.le_of_dvd one_pos hone
    omega
  have hcard : #G ≤ #(univ \ G) := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  have htot : #(univ : Finset (Finset (Fin m))) = 2 ^ m := by
    simp [Finset.card_univ, Fintype.card_finset]
  have hsd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ G)
  omega

end CS

import Mathlib

/-!
# Constant-depth circuits with `MOD q` gates

This file sets up the syntax and semantics of unbounded fan-in Boolean circuits with
`AND`, `OR`, `NOT` and `MOD q` gates, the `MOD p` Boolean function, and the class `AC⁰[q]`.

Circuits are represented as *trees*.  This is no loss of generality for the class `AC⁰[q]`:
unfolding a depth-`d`, size-`S` DAG circuit into a tree yields a tree of size at most `S ^ d`,
which is still polynomial when `d` is a constant.  Thus the class of functions defined below
is exactly `AC⁰[q]`.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`, `OR` and `MOD` gates, and `NOT` gates.
Input variables are indexed by natural numbers. -/
inductive Circuit : Type where
  | var : ℕ → Circuit
  | const : Bool → Circuit
  | cnot : Circuit → Circuit
  | cor : List Circuit → Circuit
  | cand : List Circuit → Circuit
  | cmod : List Circuit → Circuit

namespace Circuit

/-- Induction principle for circuits. -/
@[elab_as_elim]
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
def size : Circuit → ℕ
  | .var _ => 1
  | .const _ => 1
  | .cnot c => c.size + 1
  | .cor cs => (cs.map size).sum + 1
  | .cand cs => (cs.map size).sum + 1
  | .cmod cs => (cs.map size).sum + 1

/-- The depth of a circuit, i.e. the maximal number of `AND`/`OR`/`MOD` gates on a
path from the output to an input.  (`NOT` gates are not counted; this only makes the
main theorem stronger.) -/
def depth : Circuit → ℕ
  | .var _ => 0
  | .const _ => 0
  | .cnot c => c.depth
  | .cor cs => (cs.map depth).foldr max 0 + 1
  | .cand cs => (cs.map depth).foldr max 0 + 1
  | .cmod cs => (cs.map depth).foldr max 0 + 1

/-- Semantics of circuits: a `MOD q` gate outputs `true` iff the number of its inputs
that are `true` is divisible by `q`. -/
def eval (q : ℕ) : Circuit → (ℕ → Bool) → Bool
  | .var i, x => x i
  | .const b, _ => b
  | .cnot c, x => !(c.eval q x)
  | .cor cs, x => (cs.map (fun c => c.eval q x)).any id
  | .cand cs, x => (cs.map (fun c => c.eval q x)).all id
  | .cmod cs, x => decide (((cs.map (fun c => c.eval q x)).count true) % q = 0)

@[simp] theorem eval_var (q i x) : eval q (.var i) x = x i := by simp [eval]
@[simp] theorem eval_const (q b x) : eval q (.const b) x = b := by simp [eval]
@[simp] theorem eval_cnot (q c x) : eval q (.cnot c) x = !(eval q c x) := by simp [eval]
theorem eval_cor (q cs x) : eval q (.cor cs) x = (cs.map (fun c => c.eval q x)).any id := by
  simp [eval]
theorem eval_cand (q cs x) : eval q (.cand cs) x = (cs.map (fun c => c.eval q x)).all id := by
  simp [eval]
theorem eval_cmod (q cs x) :
    eval q (.cmod cs) x = decide (((cs.map (fun c => c.eval q x)).count true) % q = 0) := by
  simp [eval]

@[simp] theorem size_var (i) : (Circuit.var i).size = 1 := by simp [size]
@[simp] theorem size_const (b) : (Circuit.const b).size = 1 := by simp [size]
@[simp] theorem size_cnot (c) : (Circuit.cnot c).size = c.size + 1 := by simp [size]
@[simp] theorem size_cor (cs) : (Circuit.cor cs).size = (cs.map size).sum + 1 := by simp [size]
@[simp] theorem size_cand (cs) : (Circuit.cand cs).size = (cs.map size).sum + 1 := by simp [size]
@[simp] theorem size_cmod (cs) : (Circuit.cmod cs).size = (cs.map size).sum + 1 := by simp [size]

@[simp] theorem depth_var (i) : (Circuit.var i).depth = 0 := by simp [depth]
@[simp] theorem depth_const (b) : (Circuit.const b).depth = 0 := by simp [depth]
@[simp] theorem depth_cnot (c) : (Circuit.cnot c).depth = c.depth := by simp [depth]
@[simp] theorem depth_cor (cs) :
    (Circuit.cor cs).depth = (cs.map depth).foldr max 0 + 1 := by simp [depth]
@[simp] theorem depth_cand (cs) :
    (Circuit.cand cs).depth = (cs.map depth).foldr max 0 + 1 := by simp [depth]
@[simp] theorem depth_cmod (cs) :
    (Circuit.cmod cs).depth = (cs.map depth).foldr max 0 + 1 := by simp [depth]

theorem size_le_of_mem {cs : List Circuit} {c : Circuit} (h : c ∈ cs) :
    c.size ≤ (cs.map size).sum :=
  List.single_le_sum (by simp) _ (List.mem_map_of_mem h)

theorem depth_le_of_mem {cs : List Circuit} {c : Circuit} (h : c ∈ cs) :
    c.depth ≤ (cs.map depth).foldr max 0 := by
  induction cs with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · simp only [List.map_cons, List.foldr_cons]
      exact le_trans (ih h) (le_max_right _ _)

theorem one_le_size (c : Circuit) : 1 ≤ c.size := by
  cases c <;> simp

end Circuit

/-- `x` only uses the first `n` input variables. -/
def Supported (n : ℕ) (x : ℕ → Bool) : Prop := ∀ i, n ≤ i → x i = false

/-- The number of `true` coordinates of `x` among the first `n`. -/
def popCount (n : ℕ) (x : ℕ → Bool) : ℕ := ((Finset.range n).filter (fun i => x i = true)).card

/-- The `MOD p` function on `n` variables: `true` iff the number of ones is divisible by `p`. -/
def MOD (p n : ℕ) (x : ℕ → Bool) : Bool := decide (popCount n x % p = 0)

/-- The circuit `C` computes the Boolean function `f` of the first `n` variables. -/
def Computes (q n : ℕ) (C : Circuit) (f : (ℕ → Bool) → Bool) : Prop :=
  ∀ x, Supported n x → C.eval q x = f x

/-- `f ∈ AC⁰[q]`: there is a family of circuits with `MOD q` gates of constant depth and
polynomial size computing `f`. -/
def InAC0mod (q : ℕ) (f : ℕ → (ℕ → Bool) → Bool) : Prop :=
  ∃ d c : ℕ, ∀ n : ℕ, ∃ C : Circuit,
    C.depth ≤ d ∧ C.size ≤ (n + 2) ^ c ∧ Computes q n C (f n)

end CS

import Mathlib

/-!
# Low degree functions on the Boolean cube

For a field `F` we consider the `F`-algebra of all functions `(Fin n → Bool) → F`, and inside
it the submodule `Deg F n d` spanned by the multilinear monomials `∏ i ∈ S, x i` with
`#S ≤ d`.  This is the space of functions computed by polynomials of degree at most `d`.
-/

namespace CS

open Finset

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

variable (F : Type*) [Field F]

/-- The elements `0, 1` of `F` corresponding to a Boolean. -/
def bitv (b : Bool) : F := if b then 1 else 0

@[simp] theorem bitv_true : bitv F true = 1 := rfl
@[simp] theorem bitv_false : bitv F false = 0 := rfl

theorem bitv_mul_self (b : Bool) : bitv F b * bitv F b = bitv F b := by
  cases b <;> simp

variable {F}

/-- The multilinear monomial associated with a set of coordinates. -/
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

@[simp] theorem mon_empty {n : ℕ} : (mon (∅ : Finset (Fin n)) : Cube n → F) = 1 := by
  funext x; simp [mon]

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

theorem pow_mem_Deg {n d k : ℕ} {f : Cube n → F} (hf : f ∈ Deg F n d) :
    f ^ k ∈ Deg F n (k * d) := by
  induction k with
  | zero => simpa using one_mem_Deg
  | succ k ih =>
      rw [pow_succ]
      have := mul_mem_Deg ih hf
      exact mem_Deg_of_le this (by ring_nf; omega)

theorem bit_var_mem_Deg {n : ℕ} (i : Fin n) :
    (fun x : Cube n => bitv F (x i)) ∈ Deg F n 1 := by
  have h := mon_mem_Deg (F := F) (S := ({i} : Finset (Fin n))) (d := 1) (by simp)
  have he : (fun x : Cube n => bitv F (x i)) = (mon ({i} : Finset (Fin n)) : Cube n → F) := by
    funext x; simp [mon]
  rw [he]; exact h

open Classical in
/-- The set of points where `P` fails to compute the Boolean function `v`. -/
noncomputable def errSet {n : ℕ} (P : Cube n → F) (v : Cube n → Bool) : Finset (Cube n) :=
  Finset.univ.filter (fun x => P x ≠ bitv F (v x))

open Classical in
@[simp] theorem mem_errSet {n : ℕ} {P : Cube n → F} {v : Cube n → Bool} {x : Cube n} :
    x ∈ errSet P v ↔ P x ≠ bitv F (v x) := by simp [errSet]

open Classical in
theorem card_errSet {n : ℕ} (P : Cube n → F) (v : Cube n → Bool) :
    #(errSet P v) = ∑ x ∈ (Finset.univ : Finset (Cube n)), if P x ≠ bitv F (v x) then 1 else 0 := by
  rw [errSet, Finset.card_filter]

/-! ### Dimension bound -/

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

theorem exists_pow_le_two_pow (C e : ℕ) : ∃ k : ℕ, 1 ≤ k ∧ C * k ^ e ≤ 2 ^ k := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) e (by norm_num : (1:ℝ) < 2)
  have hC : (0:ℝ) < 1 / (C + 1) := by positivity
  obtain ⟨k, hk, hk1⟩ := ((h.def hC).and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨k, hk1, ?_⟩
  have h2 : ‖((k : ℝ)) ^ e‖ ≤ (1 / (C + 1)) * ‖(2 : ℝ) ^ k‖ := hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at h2
  have h3 : (C : ℝ) * (k : ℝ) ^ e ≤ 2 ^ k := by
    have hpos : (0:ℝ) < C + 1 := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos] at h2
    nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) k) e]
  exact_mod_cast h3

/-! ### Weights -/

/-- The number of ones of a point of the cube. -/
def wt {n : ℕ} (x : Cube n) : ℕ := #(univ.filter (fun i => x i = true))

theorem supported_ext {n : ℕ} (a : ℕ) (x : Cube n) :
    Supported (n + a) (ext (fun i => decide (i < n + a)) x) := by
  intro i hi
  have : ¬ (i < n) := by omega
  simp [ext, this]
  omega

theorem popCount_ext {n : ℕ} (a : ℕ) (x : Cube n) :
    popCount (n + a) (ext (fun i => decide (i < n + a)) x) = wt x + a := by
  classical
  unfold popCount
  have hsplit : Finset.range (n + a) = Finset.range n ∪ Finset.Ico n (n + a) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  have hdisj : Disjoint ((Finset.range n).filter
      (fun i => ext (fun i => decide (i < n + a)) x i = true))
      ((Finset.Ico n (n + a)).filter (fun i => ext (fun i => decide (i < n + a)) x i = true)) := by
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hi hi'
    omega
  rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  have h2 : (Finset.Ico n (n + a)).filter
      (fun i => ext (fun i => decide (i < n + a)) x i = true) = Finset.Ico n (n + a) := by
    refine Finset.filter_true_of_mem fun i hi => ?_
    simp only [Finset.mem_Ico] at hi
    have : ¬ (i < n) := by omega
    simp [ext, this]
    omega
  have h1 : (Finset.range n).filter (fun i => ext (fun i => decide (i < n + a)) x i = true)
      = Finset.image (Fin.val) (univ.filter (fun j : Fin n => x j = true)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, h⟩
      refine ⟨⟨i, hi⟩, ?_, rfl⟩
      simpa [ext, hi] using h
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.2, by simpa [ext, j.2] using hj⟩
  rw [h1, h2, Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Ico]
  simp [wt]

/-! ### The full product of `ζ ^ (x i)` -/

variable {F : Type*} [Field F]

theorem UU_univ_apply {n : ℕ} (ζ : F) (x : Cube n) : UU ζ univ x = ζ ^ (wt x) := by
  classical
  have h : ∀ i : Fin n, uu ζ i x = ζ ^ (if x i = true then 1 else 0) := by
    intro i
    cases h : x i <;> simp [uu, h]
  rw [UU, Finset.prod_apply, Finset.prod_congr rfl (fun i _ => h i),
    Finset.prod_pow_eq_pow_sum]
  congr 1
  simp [wt, Finset.sum_boole]

/-! ### Roots of unity -/

theorem exists_root_of_unity (F : Type*) [Field F] [IsAlgClosed F] (p : ℕ) (hp : p.Prime)
    (hchar : (p : F) ≠ 0) : ∃ z : F, z ^ p = 1 ∧ z ≠ 1 := by
  haveI : NeZero ((p : ℕ) : F) := ⟨hchar⟩
  have hdeg : (Polynomial.cyclotomic p F).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    simp only [Nat.totient_prime hp, ne_eq, Nat.cast_eq_zero]
    have := hp.two_le
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p F) hdeg
  have hprim : IsPrimitiveRoot z p := (Polynomial.isRoot_cyclotomic_iff).mp hz
  refine ⟨z, hprim.pow_eq_one, fun h => ?_⟩
  have h1 : p = orderOf z := hprim.eq_orderOf
  rw [h, orderOf_one] at h1
  have := hp.two_le
  omega

theorem zeta_pow_mod {p : ℕ} {ζ : F} (hζp : ζ ^ p = 1) (j : ℕ) : ζ ^ j = ζ ^ (j % p) := by
  conv_lhs => rw [← Nat.div_add_mod j p]
  rw [pow_add, pow_mul, hζp, one_pow, one_mul]

/-- Interpolation: the `p`-th root of unity power `ζ ^ w` is a combination of the indicators
of `w + a ≡ 0 mod p`. -/
theorem sum_zeta_eq {p : ℕ} (hp : 0 < p) {ζ : F} (hζp : ζ ^ p = 1) (w : ℕ) :
    ∑ a : Fin p, ζ ^ (p - (a : ℕ)) * (if (w + (a : ℕ)) % p = 0 then (1 : F) else 0) = ζ ^ w := by
  classical
  -- the unique `a₀ < p` with `p ∣ w + a₀`
  obtain ⟨a₀, ha₀lt, ha₀⟩ : ∃ a₀, a₀ < p ∧ p ∣ (w + a₀) := by
    rcases Nat.eq_zero_or_pos (w % p) with h | h
    · exact ⟨0, hp, by simpa using Nat.dvd_of_mod_eq_zero h⟩
    · refine ⟨p - w % p, by omega, ?_⟩
      have hw : w % p < p := Nat.mod_lt _ hp
      have h1 : w = p * (w / p) + w % p := (Nat.div_add_mod w p).symm
      refine ⟨w / p + 1, ?_⟩
      have : p * (w / p + 1) = p * (w / p) + p := by ring
      omega
  have huniq : ∀ a : ℕ, a < p → p ∣ (w + a) → a = a₀ := by
    intro a hal hdvd
    rcases le_total a a₀ with h | h
    · have : p ∣ (a₀ - a) := by
        have := Nat.dvd_sub ha₀ hdvd
        simpa [Nat.add_sub_add_left] using this
      have := Nat.eq_zero_of_dvd_of_lt this
      omega
    · have : p ∣ (a - a₀) := by
        have := Nat.dvd_sub hdvd ha₀
        simpa [Nat.add_sub_add_left] using this
      have := Nat.eq_zero_of_dvd_of_lt this
      omega
  have hkey := Finset.sum_eq_single (M := F) (s := (Finset.univ : Finset (Fin p))) (f := fun a : Fin p =>
      ζ ^ (p - (a : ℕ)) * (if (w + (a : ℕ)) % p = 0 then (1 : F) else 0))
    (⟨a₀, ha₀lt⟩ : Fin p) ?_ ?_
  · rw [hkey]
    simp only []
    rw [if_pos (Nat.dvd_iff_mod_eq_zero.mp ha₀), mul_one,
      zeta_pow_mod hζp (p - a₀), zeta_pow_mod hζp w]
    congr 1
    rcases Nat.eq_zero_or_pos a₀ with h0 | h0
    · subst h0
      have hw : p ∣ w := by simpa using ha₀
      rw [Nat.sub_zero, Nat.mod_self, Nat.dvd_iff_mod_eq_zero.mp hw]
    · obtain ⟨s, hs⟩ := ha₀
      have hs1 : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h | h
        · subst h; simp at hs; omega
        · exact h
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have hps : p * (s' + 1) = p * s' + p := by ring
      have hw : w = p * s' + (p - a₀) := by omega
      rw [hw, Nat.mul_add_mod]
  · intro b _ hb
    refine mul_eq_zero_of_right _ (if_neg ?_)
    intro hcon
    exact hb (Fin.ext (huniq b b.2 (Nat.dvd_of_mod_eq_zero hcon)))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### The final numerical contradiction -/

theorem final_numeric {m D Mid : ℕ} (hMid : 1 ≤ Mid) (hMid2 : Mid ^ 2 * (3 * m + 1) ≤ 16 ^ m)
    (hD : 64 * (D + 1) ^ 2 ≤ 27 * m) : 8 * ((D + 1) * Mid) < 3 * 4 ^ m := by
  have hsq : (8 * ((D + 1) * Mid)) ^ 2 < (3 * 4 ^ m) ^ 2 := by
    have h2 : (3 * 4 ^ m) ^ 2 = 9 * 16 ^ m := by
      rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]
      norm_num
    calc (8 * ((D + 1) * Mid)) ^ 2 = 64 * (D + 1) ^ 2 * Mid ^ 2 := by ring
      _ ≤ 27 * m * Mid ^ 2 := Nat.mul_le_mul_right _ hD
      _ < 9 * (Mid ^ 2 * (3 * m + 1)) := by nlinarith [Nat.one_le_iff_ne_zero.mp hMid]
      _ ≤ 9 * 16 ^ m := Nat.mul_le_mul_left _ hMid2
      _ = (3 * 4 ^ m) ^ 2 := h2.symm
  exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp hsq

end CS

import RequestProject.Deg
import RequestProject.Aux

/-!
# Approximating an `OR` gate by a low degree polynomial

The key probabilistic step of Razborov–Smolensky: an unbounded fan-in `OR` of functions that
are already approximated by degree `Dc` polynomials over a field of characteristic `q` is
approximated by a polynomial of degree `t (q-1) Dc`, with an additional error on at most a
`2⁻ᵗ` fraction of the cube.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {q : ℕ} [hq : Fact q.Prime] [CharP F q]

theorem card_cube (n : ℕ) : #(univ : Finset (Cube n)) = 2 ^ n := by
  simp [Finset.card_univ]

theorem or_approx {n m t Dc : ℕ}
    (g : Fin m → (Cube n → F)) (z : Fin m → Cube n → Bool)
    (hg : ∀ i, g i ∈ Deg F n Dc)
    (B : Finset (Cube n))
    (hB : ∀ x, x ∉ B → ∀ i, g i x = bitv F (z i x))
    (w : Cube n → Bool) (hw : ∀ x, w x = true ↔ ∃ i, z i x = true) :
    ∃ P ∈ Deg F n (t * (q - 1) * Dc),
      2 ^ t * #(errSet P w) ≤ 2 ^ t * #B + 2 ^ n := by
  classical
  have hq2 : 2 ≤ q := hq.out.two_le
  set Pf : (Fin t → Finset (Fin m)) → (Cube n → F) :=
    fun σ => 1 - ∏ j : Fin t, (1 - (∑ i ∈ σ j, g i) ^ (q - 1)) with hPf
  have hval : ∀ σ x, Pf σ x = 1 - ∏ j : Fin t, (1 - (∑ i ∈ σ j, g i x) ^ (q - 1)) := by
    intro σ x
    simp [hPf, Finset.prod_apply, Finset.sum_apply]
  -- degree bound
  have hdeg : ∀ σ, Pf σ ∈ Deg F n (t * (q - 1) * Dc) := by
    intro σ
    have h1 : ∀ j : Fin t, (1 - (∑ i ∈ σ j, g i) ^ (q - 1) : Cube n → F) ∈ Deg F n ((q - 1) * Dc) :=
      fun j => Submodule.sub_mem _ one_mem_Deg
        (pow_mem_Deg (Submodule.sum_mem _ (fun i _ => hg i)))
    have h2 := prod_mem_Deg (F := F) (Finset.univ : Finset (Fin t))
      (fun j => (1 - (∑ i ∈ σ j, g i) ^ (q - 1) : Cube n → F)) ((q - 1) * Dc) (fun j _ => h1 j)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    exact Submodule.sub_mem _ one_mem_Deg (by rw [mul_assoc]; exact h2)
  -- the value of the inner sums
  have hsumval : ∀ (x : Cube n), x ∉ B → ∀ (S : Finset (Fin m)),
      (∑ i ∈ S, g i x) = ((#(S.filter (fun i => z i x = true)) : ℕ) : F) := by
    intro x hx S
    have : ∀ i ∈ S, g i x = (if z i x = true then (1 : F) else 0) := by
      intro i _
      rw [hB x hx i]
      cases h : z i x <;> simp [bitv]
    rw [Finset.sum_congr rfl this, Finset.sum_boole]
  set R := (univ : Finset (Fin t → Finset (Fin m))) with hR
  have hcardR : #R = (2 ^ m) ^ t := by
    simp [hR, Finset.card_univ, Fintype.card_finset]
  -- pointwise probability bound
  have key : ∀ x, x ∉ B →
      2 ^ t * #(univ.filter (fun σ : Fin t → Finset (Fin m) => Pf σ x ≠ bitv F (w x))) ≤ #R := by
    intro x hx
    by_cases hex : ∃ i, z i x = true
    · obtain ⟨i₀, hi₀⟩ := hex
      have hwx : bitv F (w x) = 1 := by rw [(hw x).2 ⟨i₀, hi₀⟩]; rfl
      set G := univ.filter (fun S : Finset (Fin m) =>
        (#(S.filter (fun i => z i x = true))) % q = 0) with hG
      have hchar : ∀ σ : Fin t → Finset (Fin m),
          (Pf σ x ≠ bitv F (w x)) ↔ (∀ j, σ j ∈ G) := by
        intro σ
        rw [hval, hwx]
        have hfac : ∀ j : Fin t, (1 - (∑ i ∈ σ j, g i x) ^ (q - 1) : F)
            = if q ∣ #((σ j).filter (fun i => z i x = true)) then 1 else 0 := by
          intro j
          rw [hsumval x hx, natCast_pow_q F q]
          split <;> simp
        constructor
        · intro h j
          by_contra hj
          simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have : (1 - (∑ i ∈ σ j, g i x) ^ (q - 1) : F) = 0 := by
            rw [hfac j, if_neg (by rw [Nat.dvd_iff_mod_eq_zero]; exact hj)]
          exact h (by rw [Finset.prod_eq_zero (Finset.mem_univ j) this]; ring)
        · intro h
          have hprod : (∏ j : Fin t, (1 - (∑ i ∈ σ j, g i x) ^ (q - 1) : F)) = 1 := by
            refine Finset.prod_eq_one fun j _ => ?_
            have hj := h j
            simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rw [hfac j, if_pos (Nat.dvd_of_mod_eq_zero hj)]
          rw [hprod]
          intro hcon
          have : (1 : F) = 0 := by linear_combination -hcon
          exact one_ne_zero this
      have hset : (univ.filter (fun σ : Fin t → Finset (Fin m) => Pf σ x ≠ bitv F (w x)))
          = Fintype.piFinset (fun _ : Fin t => G) := by
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        exact hchar σ
      rw [hset, Fintype.card_piFinset]
      have hGcard : 2 * #G ≤ 2 ^ m := card_good_subsets q m hq2 (fun i => z i x) i₀ hi₀
      calc 2 ^ t * ∏ _j : Fin t, #G = (2 * #G) ^ t := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
        _ ≤ (2 ^ m) ^ t := Nat.pow_le_pow_left hGcard t
        _ = #R := hcardR.symm
    · push_neg at hex
      have hwx : bitv F (w x) = 0 := by
        have : w x = false := by
          by_contra hc
          exact absurd ((hw x).1 (by simpa using hc)) (by push_neg; exact hex)
        rw [this]; rfl
      have hzero : ∀ σ : Fin t → Finset (Fin m), Pf σ x = 0 := by
        intro σ
        rw [hval]
        have : ∀ j : Fin t, (1 - (∑ i ∈ σ j, g i x) ^ (q - 1) : F) = 1 := by
          intro j
          have h0 : (∑ i ∈ σ j, g i x) = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            rw [hB x hx i, show z i x = false from by simpa using hex i]
            rfl
          rw [h0, zero_pow (by omega), sub_zero]
        rw [Finset.prod_congr rfl (fun j _ => this j), Finset.prod_const_one, sub_self]
      have : (univ.filter (fun σ : Fin t → Finset (Fin m) => Pf σ x ≠ bitv F (w x))) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun σ _ => ?_
        rw [hzero σ, hwx]
        simp
      rw [this]
      simp
  -- averaging
  have hdouble : ∑ σ ∈ R, #(errSet (Pf σ) w)
      = ∑ x ∈ (univ : Finset (Cube n)),
          #(univ.filter (fun σ : Fin t → Finset (Fin m) => Pf σ x ≠ bitv F (w x))) := by
    simp only [card_errSet, Finset.card_filter]
    rw [Finset.sum_comm]
  have hptw : ∀ x ∈ (univ : Finset (Cube n)),
      2 ^ t * #(univ.filter (fun σ : Fin t → Finset (Fin m) => Pf σ x ≠ bitv F (w x)))
        ≤ (if x ∈ B then 2 ^ t * #R else 0) + #R := by
    intro x _
    by_cases hx : x ∈ B
    · rw [if_pos hx]
      have : #(univ.filter (fun σ : Fin t → Finset (Fin m) => Pf σ x ≠ bitv F (w x))) ≤ #R :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have := Nat.mul_le_mul_left (2 ^ t) this
      omega
    · have := key x hx
      omega
  have hsum : ∑ σ ∈ R, (2 ^ t * #(errSet (Pf σ) w)) ≤ ∑ _σ ∈ R, (2 ^ t * #B + 2 ^ n) := by
    rw [← Finset.mul_sum, hdouble, Finset.mul_sum]
    calc ∑ x ∈ (univ : Finset (Cube n)),
            2 ^ t * #(univ.filter (fun σ : Fin t → Finset (Fin m) => Pf σ x ≠ bitv F (w x)))
        ≤ ∑ x ∈ (univ : Finset (Cube n)), ((if x ∈ B then 2 ^ t * #R else 0) + #R) :=
          Finset.sum_le_sum hptw
      _ = #B * (2 ^ t * #R) + 2 ^ n * #R := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const, Finset.sum_const,
            card_cube, Finset.univ_inter, smul_eq_mul, smul_eq_mul]
      _ = ∑ _σ ∈ R, (2 ^ t * #B + 2 ^ n) := by
          rw [Finset.sum_const, smul_eq_mul]; ring
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le ⟨fun _ => ∅, Finset.mem_univ _⟩ hsum
  exact ⟨Pf σ, hdeg σ, hσ⟩

end CS

import RequestProject.Circuit
import RequestProject.OrApprox

/-!
# Razborov–Smolensky approximation lemma

Every circuit of depth `d` and size `S` with `AND`, `OR`, `NOT` and `MOD q` gates is computed
by a polynomial of degree `(t (q-1))^d` over a field of characteristic `q` on all but a
`S · 2⁻ᵗ` fraction of the Boolean cube.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {q : ℕ} [hq : Fact q.Prime] [CharP F q]

/-- Extend a point of the `n`-cube to a full assignment using the background assignment `β`. -/
def ext {n : ℕ} (β : ℕ → Bool) (x : Cube n) : ℕ → Bool :=
  fun i => if h : i < n then x ⟨i, h⟩ else β i

theorem bitv_not (b : Bool) : bitv F (!b) = 1 - bitv F b := by cases b <;> simp

theorem errSet_one_sub {n : ℕ} (P : Cube n → F) (v : Cube n → Bool) :
    errSet (1 - P) (fun x => !(v x)) = errSet P v := by
  ext x
  simp only [mem_errSet, Pi.sub_apply, Pi.one_apply, bitv_not]
  constructor
  · intro h hc; exact h (by rw [hc])
  · intro h hc; exact h (sub_right_injective hc)

omit hq [CharP F q] in
/-- The data extracted from the inductive hypothesis at a gate with children `cs`. -/
theorem children_approx {n : ℕ} (β : ℕ → Bool) (t : ℕ) (ht : 1 ≤ t) (hq2 : 2 ≤ q)
    (cs : List Circuit)
    (ih : ∀ c ∈ cs, ∃ P ∈ Deg F n ((t * (q - 1)) ^ c.depth),
      2 ^ t * #(errSet P (fun x => c.eval q (ext β x))) ≤ c.size * 2 ^ n) :
    ∃ (g : Fin cs.length → (Cube n → F)) (B : Finset (Cube n)),
      (∀ i, g i ∈ Deg F n ((t * (q - 1)) ^ ((cs.map Circuit.depth).foldr max 0))) ∧
      (∀ x, x ∉ B → ∀ i, g i x = bitv F ((cs.get i).eval q (ext β x))) ∧
      2 ^ t * #B ≤ (cs.map Circuit.size).sum * 2 ^ n := by
  classical
  have hbase : 1 ≤ t * (q - 1) := by
    have := Nat.mul_le_mul ht (show 1 ≤ q - 1 by omega)
    simpa using this
  choose! Pf hPf1 hPf2 using ih
  refine ⟨fun i => Pf (cs.get i), univ.biUnion (fun i : Fin cs.length =>
    errSet (Pf (cs.get i)) (fun x => (cs.get i).eval q (ext β x))), ?_, ?_, ?_⟩
  · intro i
    refine mem_Deg_of_le (hPf1 _ (List.get_mem cs i)) ?_
    exact Nat.pow_le_pow_right hbase (Circuit.depth_le_of_mem (List.get_mem cs i))
  · intro x hx i
    by_contra hc
    exact hx (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, mem_errSet.2 hc⟩)
  · calc 2 ^ t * #(univ.biUnion (fun i : Fin cs.length =>
            errSet (Pf (cs.get i)) (fun x => (cs.get i).eval q (ext β x))))
        ≤ 2 ^ t * ∑ i : Fin cs.length,
            #(errSet (Pf (cs.get i)) (fun x => (cs.get i).eval q (ext β x))) :=
          Nat.mul_le_mul_left _ (Finset.card_biUnion_le)
      _ = ∑ i : Fin cs.length,
            2 ^ t * #(errSet (Pf (cs.get i)) (fun x => (cs.get i).eval q (ext β x))) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ i : Fin cs.length, (cs.get i).size * 2 ^ n :=
          Finset.sum_le_sum fun i _ => hPf2 _ (List.get_mem cs i)
      _ = (cs.map Circuit.size).sum * 2 ^ n := by
          rw [← Finset.sum_mul, ← list_sum_map]

/-- **Razborov–Smolensky approximation lemma.** -/
theorem circuit_approx {n : ℕ} (β : ℕ → Bool) (t : ℕ) (ht : 1 ≤ t) (C : Circuit) :
    ∃ P ∈ Deg F n ((t * (q - 1)) ^ C.depth),
      2 ^ t * #(errSet P (fun x => C.eval q (ext β x))) ≤ C.size * 2 ^ n := by
  classical
  have hq2 : 2 ≤ q := hq.out.two_le
  have hbase : 1 ≤ t * (q - 1) := by
    have := Nat.mul_le_mul ht (show 1 ≤ q - 1 by omega)
    simpa using this
  induction C using Circuit.induction with
  | hvar i =>
      simp only [Circuit.depth_var, pow_zero]
      by_cases h : i < n
      · refine ⟨fun x => bitv F (x ⟨i, h⟩), bit_var_mem_Deg _, ?_⟩
        have he : errSet (fun x : Cube n => bitv F (x ⟨i, h⟩))
            (fun x => (Circuit.var i).eval q (ext β x)) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun x _ => ?_
          simp [ext, h]
        rw [errSet] at he ⊢
        rw [he]
        simp
      · refine ⟨fun _ => bitv F (β i), const_mem_Deg _, ?_⟩
        have he : errSet (fun _ : Cube n => bitv F (β i))
            (fun x => (Circuit.var i).eval q (ext β x)) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun x _ => ?_
          simp [ext, h]
        rw [errSet] at he ⊢
        rw [he]
        simp
  | hconst b =>
      simp only [Circuit.depth_const, pow_zero]
      refine ⟨fun _ => bitv F b, const_mem_Deg _, ?_⟩
      have he : errSet (fun _ : Cube n => bitv F b)
          (fun x => (Circuit.const b).eval q (ext β x)) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun x _ => ?_
        simp
      rw [errSet] at he ⊢
      rw [he]
      simp
  | hnot c ihc =>
      obtain ⟨P, hP, hPe⟩ := ihc
      refine ⟨1 - P, ?_, ?_⟩
      · rw [Circuit.depth_cnot]
        exact Submodule.sub_mem _ one_mem_Deg hP
      · have hfun : (fun x : Cube n => (Circuit.cnot c).eval q (ext β x))
            = fun x => !(c.eval q (ext β x)) := by funext x; simp
        rw [hfun, errSet_one_sub]
        exact le_trans hPe (Nat.mul_le_mul_right _ (by simp))
  | hor cs ih =>
      obtain ⟨g, B, hgdeg, hgval, hBcard⟩ := children_approx β t ht hq2 cs ih
      obtain ⟨P, hP, hPe⟩ := or_approx (F := F) (q := q) (t := t) g
        (fun i x => (cs.get i).eval q (ext β x)) hgdeg B hgval
        (fun x => (Circuit.cor cs).eval q (ext β x))
        (fun x => by
          show (Circuit.cor cs).eval q (ext β x) = true ↔ ∃ i, (cs.get i).eval q (ext β x) = true
          rw [Circuit.eval_cor]; exact list_any_iff cs _)
      refine ⟨P, ?_, ?_⟩
      · rw [Circuit.depth_cor, pow_succ, mul_comm ((t * (q - 1)) ^ _) (t * (q - 1))]
        exact hP
      · rw [Circuit.size_cor, add_mul, one_mul]
        exact le_trans hPe (Nat.add_le_add_right hBcard _)
  | hand cs ih =>
      obtain ⟨g, B, hgdeg, hgval, hBcard⟩ := children_approx β t ht hq2 cs ih
      obtain ⟨Q, hQ, hQe⟩ := or_approx (F := F) (q := q) (t := t) (fun i => 1 - g i)
        (fun i x => !((cs.get i).eval q (ext β x)))
        (fun i => Submodule.sub_mem _ one_mem_Deg (hgdeg i)) B
        (fun x hx i => by
          show (1 : Cube n → F) x - g i x = bitv F (!((cs.get i).eval q (ext β x)))
          rw [bitv_not, hgval x hx i]
          rfl)
        (fun x => !((Circuit.cand cs).eval q (ext β x)))
        (fun x => by
          show ((!((Circuit.cand cs).eval q (ext β x))) = true) ↔
            ∃ i, ((!((cs.get i).eval q (ext β x))) = true)
          rw [Circuit.eval_cand]
          constructor
          · intro h
            have h' : ¬ ((cs.map (fun c => c.eval q (ext β x))).all id = true) := by
              simpa using h
            rw [list_all_iff] at h'
            push_neg at h'
            obtain ⟨i, hi⟩ := h'
            exact ⟨i, by simpa using hi⟩
          · rintro ⟨i, hi⟩
            have : ¬ ((cs.map (fun c => c.eval q (ext β x))).all id = true) := by
              rw [list_all_iff]
              push_neg
              exact ⟨i, by simpa using hi⟩
            simpa using this)
      refine ⟨1 - Q, ?_, ?_⟩
      · rw [Circuit.depth_cand, pow_succ, mul_comm ((t * (q - 1)) ^ _) (t * (q - 1))]
        exact Submodule.sub_mem _ one_mem_Deg hQ
      · have hfun : (fun x : Cube n => (Circuit.cand cs).eval q (ext β x))
            = fun x => !(!((Circuit.cand cs).eval q (ext β x))) := by funext x; simp
        rw [hfun, errSet_one_sub]
        rw [Circuit.size_cand, add_mul, one_mul]
        exact le_trans hQe (Nat.add_le_add_right hBcard _)
  | hmod cs ih =>
      obtain ⟨g, B, hgdeg, hgval, hBcard⟩ := children_approx β t ht hq2 cs ih
      refine ⟨1 - (∑ i : Fin cs.length, g i) ^ (q - 1), ?_, ?_⟩
      · rw [Circuit.depth_cmod, pow_succ, mul_comm ((t * (q - 1)) ^ _) (t * (q - 1))]
        refine Submodule.sub_mem _ one_mem_Deg ?_
        refine mem_Deg_of_le (pow_mem_Deg (Submodule.sum_mem _ fun i _ => hgdeg i)) ?_
        exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega))
      · have hsub : errSet (1 - (∑ i : Fin cs.length, g i) ^ (q - 1))
            (fun x => (Circuit.cmod cs).eval q (ext β x)) ⊆ B := by
          intro x hx
          by_contra hxB
          refine (mem_errSet.1 hx) ?_
          have hval : (∑ i : Fin cs.length, g i) x
              = ((((cs.map (fun c => c.eval q (ext β x))).count true : ℕ)) : F) := by
            rw [Finset.sum_apply]
            rw [list_count_map]
            push_cast
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hgval x hxB i]
            cases h : (cs.get i).eval q (ext β x) <;> simp
          simp only [Pi.sub_apply, Pi.one_apply, Pi.pow_apply, hval]
          rw [natCast_pow_q F q, Circuit.eval_cmod]
          by_cases hd : q ∣ (cs.map (fun c => c.eval q (ext β x))).count true
          · rw [if_pos hd, sub_zero,
              show decide ((cs.map (fun c => c.eval q (ext β x))).count true % q = 0) = true from
                by simp [Nat.dvd_iff_mod_eq_zero.mp hd]]
            rfl
          · rw [if_neg hd, sub_self,
              show decide ((cs.map (fun c => c.eval q (ext β x))).count true % q = 0) = false from
                by simpa using fun hc => hd (Nat.dvd_iff_mod_eq_zero.mpr hc)]
            rfl
        calc 2 ^ t * #(errSet (1 - (∑ i : Fin cs.length, g i) ^ (q - 1))
              (fun x => (Circuit.cmod cs).eval q (ext β x)))
            ≤ 2 ^ t * #B := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
          _ ≤ (cs.map Circuit.size).sum * 2 ^ n := hBcard
          _ ≤ (Circuit.cmod cs).size * 2 ^ n := by
              rw [Circuit.size_cmod, add_mul, one_mul]; exact Nat.le_add_right _ _

end CS

import RequestProject.Deg
import RequestProject.Binomial

/-!
# Smolensky's dimension argument

If, on a set `A` of points of the cube `{0,1}ⁿ` (`n = 2m`), the function
`x ↦ ζ^(x₁+⋯+xₙ)` agrees with a polynomial of degree `D` (`ζ` a `p`-th root of unity), then
every function on `A` is the restriction of a polynomial of degree at most `m + D`, whence
`#A ≤ ∑_{i ≤ m+D} C(n,i)`.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {n : ℕ}

/-- `ζ ^ (x i)`, as a degree one function of `x`. -/
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
theorem centralBinom_sq_le (m : ℕ) : (Nat.centralBinom m) ^ 2 * (3 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp [Nat.centralBinom]
  | succ m ih =>
    have key := Nat.succ_mul_centralBinom_succ m
    have e1 : ((m + 1) ^ 2) * (Nat.centralBinom (m + 1)) ^ 2
        = (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2 := by
      rw [← key]; ring
    have step : ((m + 1) ^ 2) * ((Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1))
        ≤ ((m + 1) ^ 2) * 16 ^ (m + 1) := by
      have h2 : ((m + 1) ^ 2) * ((Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1))
          = (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2 * (3 * m + 4) := by
        rw [← mul_assoc, e1]; ring_nf
      have h3 : (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2 * (3 * m + 4)
          ≤ 16 * (m + 1) ^ 2 * ((Nat.centralBinom m) ^ 2 * (3 * m + 1)) := by
        have h4 : (2 * m + 1) ^ 2 * (3 * m + 4) ≤ 4 * (m + 1) ^ 2 * (3 * m + 1) := by nlinarith
        nlinarith [Nat.zero_le ((Nat.centralBinom m) ^ 2)]
      have h5 : 16 * (m + 1) ^ 2 * ((Nat.centralBinom m) ^ 2 * (3 * m + 1))
          ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
      calc ((m + 1) ^ 2) * ((Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1))
          = (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2 * (3 * m + 4) := h2
        _ ≤ 16 * (m + 1) ^ 2 * ((Nat.centralBinom m) ^ 2 * (3 * m + 1)) := h3
        _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := h5
        _ = ((m + 1) ^ 2) * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left step (by positivity)

/-- Reflection: the binomial coefficients below the middle sum to the same as those above. -/
theorem sum_choose_lt_eq (m : ℕ) :
    ∑ j ∈ range m, (2 * m).choose j = ∑ j ∈ range m, (2 * m).choose (m + 1 + j) := by
  have h := Finset.sum_range_reflect (fun j => (2 * m).choose (m + 1 + j)) m
  rw [← h]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m := Finset.mem_range.mp hj
  have : m + 1 + (m - 1 - j) = 2 * m - j := by omega
  rw [this, Nat.choose_symm (by omega)]

/-- `2 ∑_{i<m} C(2m,i) + C(2m,m) = 4^m`. -/
theorem two_mul_sum_choose_lt (m : ℕ) :
    2 * (∑ j ∈ range m, (2 * m).choose j) + (2 * m).choose m = 4 ^ m := by
  have htot : ∑ j ∈ range (2 * m + 1), (2 * m).choose j = 4 ^ m := by
    rw [Nat.sum_range_choose]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hsplit : ∑ j ∈ range (2 * m + 1), (2 * m).choose j
      = (∑ j ∈ range m, (2 * m).choose j) + (2 * m).choose m
        + ∑ j ∈ Ico (m + 1) (2 * m + 1), (2 * m).choose j := by
    rw [← Finset.sum_range_succ (fun j => (2 * m).choose j) m]
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ 2 * m + 1)]
  have hIco : ∑ j ∈ Ico (m + 1) (2 * m + 1), (2 * m).choose j
      = ∑ j ∈ range m, (2 * m).choose (m + 1 + j) := by
    rw [Finset.sum_Ico_eq_sum_range, show 2 * m + 1 - (m + 1) = m from by omega]
  rw [hsplit, hIco, ← sum_choose_lt_eq] at htot
  omega

/-- The partial sum of binomial coefficients up to `m + D`. -/
theorem two_mul_sum_choose_le (m D : ℕ) :
    2 * (∑ i ∈ range (m + D + 1), (2 * m).choose i)
      ≤ 4 ^ m + 2 * (D + 1) * ((2 * m).choose m) := by
  have hsplit : ∑ i ∈ range (m + D + 1), (2 * m).choose i
      = (∑ i ∈ range m, (2 * m).choose i) + ∑ i ∈ Ico m (m + D + 1), (2 * m).choose i := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m ≤ m + D + 1)]
  have hband : ∑ i ∈ Ico m (m + D + 1), (2 * m).choose i ≤ (D + 1) * ((2 * m).choose m) := by
    calc ∑ i ∈ Ico m (m + D + 1), (2 * m).choose i
        ≤ ∑ _i ∈ Ico m (m + D + 1), (2 * m).choose m := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := Nat.choose_le_middle i (2 * m)
          simpa [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using this
      _ = (D + 1) * ((2 * m).choose m) := by
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
          congr 1
          omega
  have h2 := two_mul_sum_choose_lt m
  have h3 : 2 * (D + 1) * ((2 * m).choose m) = 2 * ((D + 1) * ((2 * m).choose m)) := by ring
  omega

end CS

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command, so the header above is a plain comment;
-- it is repeated below as the module docstring.)

import RequestProject.Assembly

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Razborov–Smolensky theorem: for distinct primes `p` and `q`, the function `MOD p` is not
in `AC⁰[q]`, i.e. it is not computed by constant depth, polynomial size circuits with
unbounded fan-in `AND`, `OR`, `NOT` and `MOD q` gates.
-/

namespace CS

open Finset

/-- The number of "rounds" used in the polynomial approximation of a circuit of size at most
`(2m + p + 2) ^ c`. -/
def tval (p c m : ℕ) : ℕ := c * (Nat.log 2 (2 * m + p + 2) + 1) + p + 3

theorem one_le_tval (p c m : ℕ) : 1 ≤ tval p c m := by
  unfold tval; omega

theorem eight_mul_le_two_pow_tval (p c m : ℕ) :
    8 * p * (2 * m + p + 2) ^ c ≤ 2 ^ (tval p c m) := by
  set L := Nat.log 2 (2 * m + p + 2) + 1 with hL
  have h1 : 2 * m + p + 2 < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : (2 * m + p + 2) ^ c ≤ (2 ^ L) ^ c := Nat.pow_le_pow_left (le_of_lt h1) c
  have h3 : p ≤ 2 ^ p := le_of_lt Nat.lt_two_pow_self
  have h4 : 2 ^ (tval p c m) = (2 ^ L) ^ c * 2 ^ p * 8 := by
    rw [tval, ← hL, pow_add, pow_add, ← pow_mul']
    norm_num
  rw [h4]
  calc 8 * p * (2 * m + p + 2) ^ c ≤ 8 * 2 ^ p * (2 ^ L) ^ c :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) h2
    _ = (2 ^ L) ^ c * 2 ^ p * 8 := by ring

/-- The core inequality: if `MOD p` is computed by depth `d`, size `(n+2)^c` circuits with
`MOD q` gates, then for every `m` the central binomial coefficient must be large. -/
theorem main_ineq {p q d c : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hfam : ∀ n : ℕ, ∃ C : Circuit, C.depth ≤ d ∧ C.size ≤ (n + 2) ^ c ∧ Computes q n C (MOD p n))
    (m : ℕ) :
    3 * 4 ^ m ≤ 8 * (((tval p c m * (q - 1)) ^ d + 1) * ((2 * m).choose m)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set F := AlgebraicClosure (ZMod q) with hFdef
  set n := 2 * m with hn
  set t := tval p c m with htdef
  set D := (t * (q - 1)) ^ d with hDdef
  have hq2 : 2 ≤ q := hq.two_le
  have ht : 1 ≤ t := one_le_tval p c m
  have hbase : 1 ≤ t * (q - 1) := by
    have := Nat.mul_le_mul ht (show 1 ≤ q - 1 by omega)
    simpa using this
  -- a `p`-th root of unity in an algebraically closed field of characteristic `q`
  have hpF : ((p : F)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F q p]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 hdvd).symm
  obtain ⟨ζ, hζp, hζ1⟩ := exists_root_of_unity F p hp hpF
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hp.pos.ne'] at hζp
    exact zero_ne_one hζp
  -- approximating polynomials for the `p` shifted `MOD p` functions
  set S := (n + p + 2) ^ c with hS
  have hchoice : ∀ a : Fin p, ∃ P : Cube n → F, P ∈ Deg F n D ∧
      2 ^ t * #(errSet P (fun x => decide ((wt x + (a : ℕ)) % p = 0))) ≤ S * 2 ^ n := by
    intro a
    obtain ⟨C, hCd, hCs, hCc⟩ := hfam (n + (a : ℕ))
    obtain ⟨P, hP, hPe⟩ := circuit_approx (F := F) (q := q) (n := n)
        (β := fun i => decide (i < n + (a : ℕ))) t ht C
    have hev : (fun x : Cube n => C.eval q (ext (fun i => decide (i < n + (a : ℕ))) x))
        = (fun x => decide ((wt x + (a : ℕ)) % p = 0)) := by
      funext x
      rw [hCc _ (supported_ext _ x)]
      unfold CS.MOD
      rw [popCount_ext]
    refine ⟨P, mem_Deg_of_le hP (Nat.pow_le_pow_right hbase hCd), ?_⟩
    rw [← hev]
    refine le_trans hPe (Nat.mul_le_mul_right _ (le_trans hCs ?_))
    exact Nat.pow_le_pow_left (by have := a.2; omega) c
  choose Pf hPf1 hPf2 using hchoice
  set bad := univ.biUnion
    (fun a : Fin p => errSet (Pf a) (fun x => decide ((wt x + (a : ℕ)) % p = 0))) with hbad
  set A := (univ : Finset (Cube n)) \ bad with hAdef
  -- the total error is small
  have hcube : #(univ : Finset (Cube n)) = 2 ^ n := card_cube n
  have hstep : 2 ^ t * #bad ≤ p * (S * 2 ^ n) := by
    have h1 : #bad ≤ ∑ a : Fin p,
        #(errSet (Pf a) (fun x => decide ((wt x + (a : ℕ)) % p = 0))) := Finset.card_biUnion_le
    calc 2 ^ t * #bad ≤ 2 ^ t * ∑ a : Fin p,
          #(errSet (Pf a) (fun x => decide ((wt x + (a : ℕ)) % p = 0))) :=
            Nat.mul_le_mul_left _ h1
      _ = ∑ a : Fin p, 2 ^ t *
            #(errSet (Pf a) (fun x => decide ((wt x + (a : ℕ)) % p = 0))) := Finset.mul_sum _ _ _
      _ ≤ ∑ _a : Fin p, S * 2 ^ n := Finset.sum_le_sum fun a _ => hPf2 a
      _ = p * (S * 2 ^ n) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  have h8bad : 8 * #bad ≤ 2 ^ n := by
    have hpow : 0 < 2 ^ t := Nat.two_pow_pos t
    refine Nat.le_of_mul_le_mul_left ?_ hpow
    calc 2 ^ t * (8 * #bad) = 8 * (2 ^ t * #bad) := by ring
      _ ≤ 8 * (p * (S * 2 ^ n)) := Nat.mul_le_mul_left _ hstep
      _ = (8 * p * S) * 2 ^ n := by ring
      _ ≤ 2 ^ t * 2 ^ n := Nat.mul_le_mul_right _ (eight_mul_le_two_pow_tval p c m)
  have hAcard : 7 * 2 ^ n ≤ 8 * #A := by
    have hsub : bad ⊆ (univ : Finset (Cube n)) := Finset.subset_univ _
    have hcs : #A + #bad = 2 ^ n := by
      rw [hAdef, Finset.card_sdiff_add_card_eq_card hsub, hcube]
    omega
  -- the interpolating polynomial
  have hPcomb : (∑ a : Fin p, ζ ^ (p - (a : ℕ)) • Pf a) ∈ Deg F n D :=
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hPf1 a)
  have hAval : ∀ x ∈ A, UU ζ univ x = (∑ a : Fin p, ζ ^ (p - (a : ℕ)) • Pf a) x := by
    intro x hxA
    have hx : ∀ a : Fin p, Pf a x = bitv F (decide ((wt x + (a : ℕ)) % p = 0)) := by
      intro a
      by_contra hc
      exact (Finset.mem_sdiff.1 hxA).2
        (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ a, mem_errSet.2 hc⟩)
    rw [UU_univ_apply, Finset.sum_apply, ← sum_zeta_eq hp.pos hζp (wt x)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hx a]
    congr 1
    by_cases h : (wt x + (a : ℕ)) % p = 0 <;> simp [h, bitv]
  have hsmol := smolensky_dim (F := F) (n := n) (m := m) (D := D) hn hζ0 hζ1 A _ hPcomb hAval
  -- combine with the binomial estimate
  have hbin := two_mul_sum_choose_le m D
  have hbin' : 2 * (∑ i ∈ Finset.range (m + D + 1), (2 * m).choose i)
      ≤ 4 ^ m + 2 * ((D + 1) * ((2 * m).choose m)) := by
    calc 2 * (∑ i ∈ Finset.range (m + D + 1), (2 * m).choose i)
        ≤ 4 ^ m + 2 * (D + 1) * ((2 * m).choose m) := hbin
      _ = 4 ^ m + 2 * ((D + 1) * ((2 * m).choose m)) := by ring
  have h2n : (2 : ℕ) ^ n = 4 ^ m := by
    rw [hn, pow_mul]
    norm_num
  rw [h2n] at hAcard
  rw [← hn] at hbin'
  omega

/-! ### Sanity check: the class is nonempty and contains `MOD q` -/

theorem count_true_range (x : ℕ → Bool) (n : ℕ) :
    ((List.range n).map x).count true = popCount n x := by
  induction n with
  | zero => simp [popCount]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih]
    unfold popCount
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : x n = true
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · rw [if_neg h]
      simp [h]

/-- `MOD q` itself is in `AC⁰[q]` (a single `MOD q` gate computes it); in particular the class
`AC⁰[q]` is not empty and the definitions above are not vacuous. -/
theorem MOD_self_mem (q : ℕ) : InAC0mod q (MOD q) := by
  have hd : ∀ l : List ℕ, List.foldr max 0 (List.map (Circuit.depth ∘ Circuit.var) l) = 0 := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  have hs : ∀ l : List ℕ, (List.map (Circuit.size ∘ Circuit.var) l).sum = l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [ih, Nat.add_comm]
  refine ⟨1, 1, fun n => ⟨Circuit.cmod ((List.range n).map Circuit.var), ?_, ?_, ?_⟩⟩
  · simp [Circuit.depth_cmod, hd]
  · simp [Circuit.size_cmod, hs]
  · intro x _
    rw [Circuit.eval_cmod]
    have h : (List.map (fun c => Circuit.eval q c x) ((List.range n).map Circuit.var))
        = (List.range n).map x := by
      rw [List.map_map]
      exact List.map_congr_left (by intro i _; simp)
    rw [h, count_true_range]
    rfl

/-- **Razborov–Smolensky theorem**: for distinct primes `p` and `q`, `MOD p ∉ AC⁰[q]`. -/
theorem razborov_smolensky (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ InAC0mod q (MOD p) := by
  rintro ⟨d, c, hfam⟩
  set N := c + p + 4 with hN
  set G := N * (q - 1) + 1 with hG
  obtain ⟨k, hk1, hk⟩ :=
    exists_pow_le_two_pow (256 * G ^ (2 * d) * (N + 1) ^ (2 * d)) (2 * d)
  set m := 2 ^ k with hm
  set t := tval p c m with ht
  set D := (t * (q - 1)) ^ d with hD
  -- `t` is at most `N * (k + N)`
  have hlog : Nat.log 2 (2 * m + p + 2) ≤ k + p + 3 := by
    have h1 : 2 * m + p + 2 ≤ 2 ^ (k + p + 3) := by
      have hp2 : p + 2 ≤ 2 ^ (p + 2) := le_of_lt Nat.lt_two_pow_self
      have e1 : 2 * m = 2 ^ (k + 1) := by rw [hm, pow_succ]; ring
      have e2 : (2 : ℕ) ^ (k + 1) ≤ 2 ^ (k + p + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e3 : (2 : ℕ) ^ (p + 2) ≤ 2 ^ (k + p + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e4 : (2 : ℕ) ^ (k + p + 2) + 2 ^ (k + p + 2) = 2 ^ (k + p + 3) := by
        rw [show k + p + 3 = (k + p + 2) + 1 by omega, pow_succ]; ring
      omega
    calc Nat.log 2 (2 * m + p + 2) ≤ Nat.log 2 (2 ^ (k + p + 3)) :=
          Nat.log_mono_right h1
      _ = k + p + 3 := Nat.log_pow (by norm_num) _
  have htle : t ≤ N * (k + N) := by
    have h1 : t ≤ c * (k + p + 4) + p + 3 := by
      rw [ht, tval]
      have := hlog
      nlinarith [Nat.zero_le c]
    have h2 : c * (k + p + 4) + p + 3 ≤ N * (k + N) := by
      have hkN : 1 ≤ k + N := by omega
      nlinarith [Nat.zero_le c, Nat.zero_le k, Nat.zero_le p]
    omega
  have hDle : D ≤ G ^ d * (k + N) ^ d := by
    have h1 : t * (q - 1) ≤ G * (k + N) := by
      calc t * (q - 1) ≤ (N * (k + N)) * (q - 1) := Nat.mul_le_mul_right _ htle
        _ = (N * (q - 1)) * (k + N) := by ring
        _ ≤ G * (k + N) := Nat.mul_le_mul_right _ (by omega)
    calc D ≤ (G * (k + N)) ^ d := Nat.pow_le_pow_left h1 d
      _ = G ^ d * (k + N) ^ d := by rw [mul_pow]
  -- the numerical hypothesis of `final_numeric`
  have hGpos : 1 ≤ G ^ d := Nat.one_le_pow _ _ (by omega)
  have hkNpos : 1 ≤ (k + N) ^ d := Nat.one_le_pow _ _ (by omega)
  have hDbound : 64 * (D + 1) ^ 2 ≤ 27 * m := by
    have h1 : D + 1 ≤ 2 * (G ^ d * (k + N) ^ d) := by
      have : 1 ≤ G ^ d * (k + N) ^ d := Nat.one_le_iff_ne_zero.2 (by positivity)
      omega
    have h2 : (D + 1) ^ 2 ≤ 4 * (G ^ (2 * d) * (k + N) ^ (2 * d)) := by
      calc (D + 1) ^ 2 ≤ (2 * (G ^ d * (k + N) ^ d)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 4 * ((G ^ d) ^ 2 * ((k + N) ^ d) ^ 2) := by ring
        _ = 4 * (G ^ (2 * d) * (k + N) ^ (2 * d)) := by
            rw [← pow_mul, ← pow_mul, mul_comm d 2]
    have h3 : (k + N) ^ (2 * d) ≤ (N + 1) ^ (2 * d) * k ^ (2 * d) := by
      calc (k + N) ^ (2 * d) ≤ (k * (N + 1)) ^ (2 * d) := by
            refine Nat.pow_le_pow_left ?_ _
            nlinarith [Nat.zero_le N, Nat.zero_le k]
        _ = (N + 1) ^ (2 * d) * k ^ (2 * d) := by rw [mul_pow]; ring
    have h4 : 64 * (D + 1) ^ 2
        ≤ (256 * G ^ (2 * d) * (N + 1) ^ (2 * d)) * k ^ (2 * d) := by
      calc 64 * (D + 1) ^ 2 ≤ 64 * (4 * (G ^ (2 * d) * (k + N) ^ (2 * d))) :=
            Nat.mul_le_mul_left _ h2
        _ = 256 * G ^ (2 * d) * (k + N) ^ (2 * d) := by ring
        _ ≤ 256 * G ^ (2 * d) * ((N + 1) ^ (2 * d) * k ^ (2 * d)) :=
            Nat.mul_le_mul_left _ h3
        _ = (256 * G ^ (2 * d) * (N + 1) ^ (2 * d)) * k ^ (2 * d) := by ring
    calc 64 * (D + 1) ^ 2 ≤ (256 * G ^ (2 * d) * (N + 1) ^ (2 * d)) * k ^ (2 * d) := h4
      _ ≤ 2 ^ k := hk
      _ = m := hm.symm
      _ ≤ 27 * m := by omega
  -- the two inequalities contradict each other
  have hMid : 1 ≤ (2 * m).choose m := Nat.choose_pos (by omega)
  have hMid2 : ((2 * m).choose m) ^ 2 * (3 * m + 1) ≤ 16 ^ m := by
    have := centralBinom_sq_le m
    rwa [Nat.centralBinom] at this
  have hlt := final_numeric hMid hMid2 hDbound
  have hge := main_ineq hp hq hpq hfam m
  rw [← ht, ← hD] at hge
  omega

end CS

