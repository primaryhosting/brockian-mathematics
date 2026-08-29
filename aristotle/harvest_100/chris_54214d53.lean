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

/-
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/

theorem sum_split {M : Type*} [AddCommMonoid M] (w v : ℕ) (F : (Fin (w + v) → Bool) → M) :
    ∑ y : Fin (w + v) → Bool, F y
      = ∑ y1 : Fin w → Bool, ∑ y2 : Fin v → Bool, F (Fin.append y1 y2) := by
  have h := Equiv.sum_comp (Fin.appendEquiv w v) F
  rw [← h, Fintype.sum_prod_type]
  rfl

/-- The sub-witness of `y` of length `w` starting at position `k`. -/
def subw (k w W : ℕ) (h : k + w ≤ W) (y : Fin W → Bool) : Fin w → Bool :=
  fun j => y ⟨k + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 k) h⟩

theorem append_apply_left {w v : ℕ} (y1 : Fin w → Bool) (y2 : Fin v → Bool)
    (i : Fin (w + v)) (j : Fin w) (hij : (i : ℕ) = (j : ℕ)) :
    Fin.append y1 y2 i = y1 j := by
  have : i = Fin.castAdd v j := Fin.ext (by simpa using hij)
  rw [this, Fin.append_left]

theorem append_apply_right {w v : ℕ} (y1 : Fin w → Bool) (y2 : Fin v → Bool)
    (i : Fin (w + v)) (j : Fin v) (hij : (i : ℕ) = w + (j : ℕ)) :
    Fin.append y1 y2 i = y2 j := by
  have : i = Fin.natAdd w j := Fin.ext (by simpa using hij)
  rw [this, Fin.append_right]

theorem subw_append_left (w v : ℕ) (h : 0 + w ≤ w + v) (y1 : Fin w → Bool)
    (y2 : Fin v → Bool) : subw 0 w (w + v) h (Fin.append y1 y2) = y1 := by
  funext j
  exact append_apply_left y1 y2 _ j (by simp)

theorem subw_append_right (w v : ℕ) (h : w + v ≤ w + v) (y1 : Fin w → Bool)
    (y2 : Fin v → Bool) : subw w v (w + v) h (Fin.append y1 y2) = y2 := by
  funext j
  exact append_apply_right y1 y2 _ j (by simp [subw])

/-! ### Views: reading a block of the witness -/

/-- `view n w k f` is `f` applied to the assignment that keeps the input variables
`< n`, reads the witness block of length `w` starting at position `n + k`, and is
`false` elsewhere. -/
def view (n w k : ℕ) (f : Assign → Bool) : Assign → Bool :=
  fun a => f (fun i => if i < n then a i else if i < n + w then a (i + k) else false)

theorem hasFml_view {Q : (Assign → Bool) → Prop} {s : ℕ} {f : Assign → Bool}
    (h : HasFml Q s f) (n w k : ℕ) : HasFml Q (2 * s) (view n w k f) := by
  have hg : ∀ i : ℕ, HasFml Q 1
      (fun a : Assign => if i < n then a i else if i < n + w then a (i + k) else false) := by
    intro i
    by_cases h1 : i < n
    · simpa [h1] using HasFml.var i
    · by_cases h2 : i < n + w
      · simpa [h1, h2] using HasFml.var (i + k)
      · simpa [h1, h2] using HasFml.const (Q := Q) false
  have := HasFml.subst h hg
  exact HasFml.mono this (by omega)

theorem view_ext {n w k W : ℕ} (h : k + w ≤ W) (f : Assign → Bool) (x : Assign)
    (y : Fin W → Bool) :
    view n w k f (ext n W x y) = f (ext n w x (subw k w W h y)) := by
  unfold view
  congr 1
  funext i
  by_cases h1 : i < n
  · simp [h1, ext_lt h1]
  · by_cases h2 : i < n + w
    · have hiw : i - n < w := by omega
      have hik : i + k = n + (k + (i - n)) := by omega
      have hlt : k + (i - n) < W := by omega
      rw [if_neg h1, if_pos h2, hik, ext_ge hlt]
      rw [ext]
      simp only [dif_neg h1, dif_pos hiw]
      simp [subw]
    · have hiw : ¬ (i - n < w) := by omega
      rw [if_neg h1, if_neg h2]
      rw [ext]
      simp [h1, hiw]

/-! ### Big conjunctions -/

/-- Conjunction of a list of Boolean functions. -/
def bigAnd : List (Assign → Bool) → (Assign → Bool)
  | [] => fun _ => true
  | f :: fs => fun a => f a && bigAnd fs a

theorem bigAnd_eq_true {l : List (Assign → Bool)} {a : Assign} :
    bigAnd l a = true ↔ ∀ f ∈ l, f a = true := by
  induction l with
  | nil => simp [bigAnd]
  | cons f fs ih => simp [bigAnd, ih]

theorem hasFml_bigAnd {Q : (Assign → Bool) → Prop} {s : ℕ} :
    ∀ (l : List (Assign → Bool)), (∀ f ∈ l, HasFml Q s f) →
      HasFml Q (l.length * (s + 1) + 1) (bigAnd l)
  | [], _ => by simpa [bigAnd] using HasFml.const (Q := Q) true
  | f :: fs, hl => by
      have hf : HasFml Q s f := hl f (by simp)
      have hfs : HasFml Q (fs.length * (s + 1) + 1) (bigAnd fs) :=
        hasFml_bigAnd fs (fun g hg => hl g (by simp [hg]))
      have := HasFml.and hf hfs
      refine HasFml.mono (this.congr' ?_) ?_
      · intro a; rfl
      · simp [List.length_cons]; ring_nf; omega

/-- The witness block of length `len` starting at position `n + off` is all-zero. -/
def zerosAt (n off len : ℕ) : Assign → Bool :=
  bigAnd ((List.range len).map (fun j => fun a : Assign => !a (n + off + j)))

theorem hasFml_zerosAt {Q : (Assign → Bool) → Prop} (n off len : ℕ) :
    HasFml Q (len * 3 + 1) (zerosAt n off len) := by
  have h : ∀ f ∈ (List.range len).map (fun j => fun a : Assign => !a (n + off + j)),
      HasFml Q 2 f := by
    intro f hf
    simp only [List.mem_map, List.mem_range] at hf
    obtain ⟨j, _, rfl⟩ := hf
    exact HasFml.not (HasFml.var (n + off + j))
  have := hasFml_bigAnd _ h
  simpa [zerosAt, List.length_map, List.length_range] using this

theorem zerosAt_ext {n off len W : ℕ} (h : off + len ≤ W) (x : Assign) (y : Fin W → Bool) :
    zerosAt n off len (ext n W x y) = true ↔ ∀ j : Fin len, y ⟨off + j.1, by omega⟩ = false := by
  rw [zerosAt, bigAnd_eq_true]
  constructor
  · intro hh j
    have hj : (fun a : Assign => !a (n + off + j.1)) ∈
        (List.range len).map (fun j => fun a : Assign => !a (n + off + j)) := by
      simp only [List.mem_map, List.mem_range]
      exact ⟨j.1, j.2, rfl⟩
    have := hh _ hj
    have hlt : off + j.1 < W := by omega
    have hval : ext n W x y (n + (off + j.1)) = y ⟨off + j.1, hlt⟩ := ext_ge hlt
    have hidx : n + off + j.1 = n + (off + j.1) := by omega
    rw [hidx, hval] at this
    simpa using this
  · intro hh f hf
    simp only [List.mem_map, List.mem_range] at hf
    obtain ⟨j, hj, rfl⟩ := hf
    have hlt : off + j < W := by omega
    have hval : ext n W x y (n + (off + j)) = y ⟨off + j, hlt⟩ := ext_ge hlt
    have hidx : n + off + j = n + (off + j) := by omega
    simp only [hidx, hval]
    have := hh ⟨j, hj⟩
    simp only at this
    simp [this]

/-! ### Gap data -/

/-- A description of a "gap function": a witness length together with predicates
describing the accepting (`pos`) and rejecting (`neg`) witnesses.  The value is the
number of accepting witnesses minus the number of rejecting ones. -/
structure GapData where
  w : ℕ
  pos : Assign → Bool
  neg : Assign → Bool

namespace GapData

/-- The weight of a single witness. -/
def wt (d : GapData) (a : Assign) : ℤ := if d.pos a then 1 else if d.neg a then -1 else 0

/-- The value of the gap function on the length-`n` input `x`. -/
def val (d : GapData) (n : ℕ) (x : Assign) : ℤ := ∑ y : Fin d.w → Bool, d.wt (ext n d.w x y)

/-- Well-formedness: both predicates are computed by formulas of size at most `s`, and
they are disjoint. -/
structure Ok (Q : (Assign → Bool) → Prop) (s : ℕ) (d : GapData) : Prop where
  hpos : HasFml Q s d.pos
  hneg : HasFml Q s d.neg
  hdisj : ∀ a, d.pos a = true → d.neg a = true → False

theorem Ok.mono {Q : (Assign → Bool) → Prop} {s t : ℕ} {d : GapData} (h : d.Ok Q s)
    (hst : s ≤ t) : d.Ok Q t :=
  ⟨HasFml.mono h.hpos hst, HasFml.mono h.hneg hst, h.hdisj⟩

/-! #### Indicator of a predicate -/

/-- The gap function with value `1` if `f` holds and `0` otherwise. -/
def ofPred (f : Assign → Bool) : GapData := ⟨0, f, fun _ => false⟩

theorem ofPred_val (f : Assign → Bool) (n : ℕ) (x : Assign) :
    (ofPred f).val n x = if f (trunc n x) then 1 else 0 := by
  show ∑ y : Fin 0 → Bool, (ofPred f).wt (ext n 0 x y) = _
  rw [Fintype.sum_unique, ext_zero]
  simp [wt, ofPred]

theorem ofPred_ok {Q : (Assign → Bool) → Prop} {s : ℕ} {f : Assign → Bool}
    (h : HasFml Q s f) : (ofPred f).Ok Q (s + 1) :=
  ⟨HasFml.mono h (by omega), HasFml.mono (HasFml.const (Q := Q) false) (by omega),
    by intro a _ hb; simp [ofPred] at hb⟩

/-! #### The constant one, with a prescribed witness length -/

/-- The gap function with constant value `1`, using witnesses of length `k` (only the
all-zero witness counts). -/
def done (n k : ℕ) : GapData := ⟨k, zerosAt n 0 k, fun _ => false⟩

theorem done_val (n k : ℕ) (x : Assign) : (done n k).val n x = 1 := by
  show ∑ y : Fin k → Bool, (done n k).wt (ext n k x y) = 1
  rw [Finset.sum_eq_single (fun _ => false : Fin k → Bool)]
  · have h : zerosAt n 0 k (ext n k x (fun _ => false)) = true := by
      rw [zerosAt_ext (by omega)]
      intro j; rfl
    simp [wt, done, h]
  · intro b _ hb
    have h : zerosAt n 0 k (ext n k x b) = false := by
      rcases Bool.eq_false_or_eq_true (zerosAt n 0 k (ext n k x b)) with hcon | hcon
      · exfalso
        have hz := (zerosAt_ext (n := n) (off := 0) (len := k) (W := k) (by omega) x b).1 hcon
        exact hb (funext fun j => by simpa using hz ⟨j.1, j.2⟩)
      · exact hcon
    simp [wt, done, h]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem done_ok {Q : (Assign → Bool) → Prop} (n k : ℕ) : (done n k).Ok Q (3 * k + 1) :=
  ⟨by simpa [done] using (hasFml_zerosAt (Q := Q) n 0 k).mono (by omega),
    HasFml.mono (HasFml.const (Q := Q) false) (by omega),
    by intro a _ hb; simp [done] at hb⟩

/-! #### Negation -/

/-- The gap function with the opposite value. -/
def dneg (d : GapData) : GapData := ⟨d.w, d.neg, d.pos⟩

theorem wt_dneg (d : GapData) (hd : ∀ a, d.pos a = true → d.neg a = true → False)
    (a : Assign) : (dneg d).wt a = - d.wt a := by
  simp only [wt, dneg]
  have hda := hd a
  by_cases hp : d.pos a = true <;> by_cases hn : d.neg a = true <;>
    simp [hp, hn] at hda ⊢

theorem dneg_val (d : GapData) (hd : ∀ a, d.pos a = true → d.neg a = true → False)
    (n : ℕ) (x : Assign) : (dneg d).val n x = - d.val n x := by
  show ∑ y : Fin d.w → Bool, (dneg d).wt (ext n d.w x y) = _
  rw [val, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun y _ => wt_dneg d hd _

theorem dneg_ok {Q : (Assign → Bool) → Prop} {s : ℕ} {d : GapData} (h : d.Ok Q s) :
    (dneg d).Ok Q s :=
  ⟨h.hneg, h.hpos, fun a h1 h2 => h.hdisj a h2 h1⟩

/-! #### Products -/

/-- The product of two gap functions: the witness is the concatenation of the two
witnesses. -/
def dmul (n : ℕ) (d1 d2 : GapData) : GapData where
  w := d1.w + d2.w
  pos := fun a => (view n d1.w 0 d1.pos a && view n d2.w d1.w d2.pos a) ||
                  (view n d1.w 0 d1.neg a && view n d2.w d1.w d2.neg a)
  neg := fun a => (view n d1.w 0 d1.pos a && view n d2.w d1.w d2.neg a) ||
                  (view n d1.w 0 d1.neg a && view n d2.w d1.w d2.pos a)

theorem wt_mul_aux (p1 n1 p2 n2 : Bool) (h1 : p1 = true → n1 = true → False)
    (h2 : p2 = true → n2 = true → False) :
    (if (p1 && p2) || (n1 && n2) then (1 : ℤ) else if (p1 && n2) || (n1 && p2) then -1 else 0)
      = (if p1 then (1 : ℤ) else if n1 then -1 else 0) *
        (if p2 then (1 : ℤ) else if n2 then -1 else 0) := by
  revert h1 h2
  cases p1 <;> cases n1 <;> cases p2 <;> cases n2 <;> simp

theorem dmul_val (n : ℕ) (x : Assign) (d1 d2 : GapData)
    (h1 : ∀ a, d1.pos a = true → d1.neg a = true → False)
    (h2 : ∀ a, d2.pos a = true → d2.neg a = true → False) :
    (dmul n d1 d2).val n x = d1.val n x * d2.val n x := by
  show ∑ y : Fin (d1.w + d2.w) → Bool, (dmul n d1 d2).wt (ext n (d1.w + d2.w) x y) = _
  rw [sum_split d1.w d2.w, val, val, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ => ?_
  have e1 : ∀ f : Assign → Bool,
      view n d1.w 0 f (ext n (d1.w + d2.w) x (Fin.append y1 y2)) = f (ext n d1.w x y1) := by
    intro f
    rw [view_ext (by omega) f x (Fin.append y1 y2), subw_append_left]
  have e2 : ∀ f : Assign → Bool,
      view n d2.w d1.w f (ext n (d1.w + d2.w) x (Fin.append y1 y2)) = f (ext n d2.w x y2) := by
    intro f
    rw [view_ext (by omega) f x (Fin.append y1 y2), subw_append_right]
  simp only [wt, dmul, e1, e2]
  exact wt_mul_aux _ _ _ _ (h1 _) (h2 _)

theorem dmul_ok {Q : (Assign → Bool) → Prop} {s : ℕ} {d1 d2 : GapData} (n : ℕ)
    (k1 : d1.Ok Q s) (k2 : d2.Ok Q s) : (dmul n d1 d2).Ok Q (8 * s + 3) := by
  have v1p := hasFml_view k1.hpos n d1.w 0
  have v1n := hasFml_view k1.hneg n d1.w 0
  have v2p := hasFml_view k2.hpos n d2.w d1.w
  have v2n := hasFml_view k2.hneg n d2.w d1.w
  refine ⟨?_, ?_, ?_⟩
  · exact HasFml.mono (HasFml.or (HasFml.and v1p v2p) (HasFml.and v1n v2n)) (by omega)
  · exact HasFml.mono (HasFml.or (HasFml.and v1p v2n) (HasFml.and v1n v2p)) (by omega)
  · intro a hp hn
    simp only [dmul, Bool.or_eq_true, Bool.and_eq_true] at hp hn
    have d1d := k1.hdisj (fun i => if i < n then a i else if i < n + d1.w then a (i + 0) else false)
    have d2d := k2.hdisj (fun i => if i < n then a i else if i < n + d2.w then a (i + d1.w) else false)
    simp only [view] at hp hn d1d d2d
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hn with ⟨hn1, hn2⟩ | ⟨hn1, hn2⟩
    · exact d2d hp2 hn2
    · exact d1d hp1 hn1
    · exact d1d hn1 hp1
    · exact d2d hn2 hp2

/-! #### Exponential sums -/

/-- Summing a gap function (for inputs of length `n + v`) over all extensions of the
length-`n` input by `v` bits. -/
def dexpsum (v : ℕ) (d : GapData) : GapData := ⟨v + d.w, d.pos, d.neg⟩

theorem dexpsum_val (v : ℕ) (d : GapData) (n : ℕ) (x : Assign) :
    (dexpsum v d).val n x = ∑ z : Fin v → Bool, d.val (n + v) (ext n v x z) := by
  show ∑ y : Fin (v + d.w) → Bool, d.wt (ext n (v + d.w) x y) = _
  rw [sum_split v d.w]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [val]
  refine Finset.sum_congr rfl fun y2 _ => ?_
  rw [ext_append]

theorem dexpsum_ok {Q : (Assign → Bool) → Prop} {s : ℕ} {d : GapData} (v : ℕ)
    (k : d.Ok Q s) : (dexpsum v d).Ok Q s := ⟨k.hpos, k.hneg, k.hdisj⟩

/-! #### Sums -/

theorem sum_fin_one_bool {M : Type*} [AddCommMonoid M] (F : (Fin 1 → Bool) → M) :
    ∑ y : Fin 1 → Bool, F y = F (fun _ => false) + F (fun _ => true) := by
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) Bool).symm F]
  rw [Fintype.sum_bool]
  have e : ∀ b : Bool, ((Equiv.funUnique (Fin 1) Bool).symm b) = (fun _ => b : Fin 1 → Bool) :=
    fun b => funext fun _ => rfl
  rw [e, e, add_comm]

/-- The sum of two gap functions with the *same* witness length; one extra bit of
witness selects which of the two is used. -/
def daddEq (n : ℕ) (d1 d2 : GapData) : GapData where
  w := d1.w + 1
  pos := fun a => (!a (n + d1.w) && view n d1.w 0 d1.pos a) ||
                  (a (n + d1.w) && view n d1.w 0 d2.pos a)
  neg := fun a => (!a (n + d1.w) && view n d1.w 0 d1.neg a) ||
                  (a (n + d1.w) && view n d1.w 0 d2.neg a)

theorem daddEq_val (n : ℕ) (x : Assign) (d1 d2 : GapData) (hw : d2.w = d1.w) :
    (daddEq n d1 d2).val n x = d1.val n x + d2.val n x := by
  obtain ⟨w2, p2, q2⟩ := d2
  simp only at hw
  subst hw
  show ∑ y : Fin (d1.w + 1) → Bool, (daddEq n d1 ⟨d1.w, p2, q2⟩).wt (ext n (d1.w + 1) x y) = _
  rw [sum_split d1.w 1, val, val, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y1 _ => ?_
  rw [sum_fin_one_bool]
  have hb : ∀ b : Fin 1 → Bool,
      ext n (d1.w + 1) x (Fin.append y1 b) (n + d1.w) = b ⟨0, by omega⟩ := by
    intro b
    rw [ext_ge (by omega)]
    exact append_apply_right y1 b _ _ (by simp)
  have e1 : ∀ (f : Assign → Bool) (b : Fin 1 → Bool),
      view n d1.w 0 f (ext n (d1.w + 1) x (Fin.append y1 b)) = f (ext n d1.w x y1) := by
    intro f b
    rw [view_ext (by omega) f x (Fin.append y1 b), subw_append_left]
  simp only [wt, daddEq, hb, e1]
  simp

theorem daddEq_ok {Q : (Assign → Bool) → Prop} {s : ℕ} {d1 d2 : GapData} (n : ℕ)
    (k1 : d1.Ok Q s) (k2 : d2.Ok Q s) : (daddEq n d1 d2).Ok Q (4 * s + 6) := by
  have v1p := hasFml_view k1.hpos n d1.w 0
  have v1n := hasFml_view k1.hneg n d1.w 0
  have v2p := hasFml_view k2.hpos n d1.w 0
  have v2n := hasFml_view k2.hneg n d1.w 0
  have hvar : HasFml Q 1 (fun a : Assign => a (n + d1.w)) := HasFml.var _
  have hnvar : HasFml Q 2 (fun a : Assign => !a (n + d1.w)) := HasFml.not hvar
  refine ⟨?_, ?_, ?_⟩
  · exact HasFml.mono (HasFml.or (HasFml.and hnvar v1p) (HasFml.and hvar v2p)) (by omega)
  · exact HasFml.mono (HasFml.or (HasFml.and hnvar v1n) (HasFml.and hvar v2n)) (by omega)
  · intro a hp hn
    simp only [daddEq, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hp hn
    have d1d := k1.hdisj (fun i => if i < n then a i else if i < n + d1.w then a (i + 0) else false)
    have d2d := k2.hdisj (fun i => if i < n then a i else if i < n + d1.w then a (i + 0) else false)
    simp only [view] at hp hn d1d d2d
    rcases hp with ⟨hb1, hp⟩ | ⟨hb1, hp⟩ <;> rcases hn with ⟨hb2, hn⟩ | ⟨hb2, hn⟩
    · exact d1d hp hn
    · rw [hb1] at hb2; exact Bool.noConfusion hb2
    · rw [hb1] at hb2; exact Bool.noConfusion hb2
    · exact d2d hp hn

/-- The sum of two gap functions. -/
def dadd (n : ℕ) (d1 d2 : GapData) : GapData :=
  daddEq n (dmul n d1 (done n d2.w)) (dmul n (done n d1.w) d2)

theorem dadd_val (n : ℕ) (x : Assign) (d1 d2 : GapData)
    (h1 : ∀ a, d1.pos a = true → d1.neg a = true → False)
    (h2 : ∀ a, d2.pos a = true → d2.neg a = true → False) :
    (dadd n d1 d2).val n x = d1.val n x + d2.val n x := by
  have hd1 : ∀ a, (done n d1.w).pos a = true → (done n d1.w).neg a = true → False := by
    intro a _ hb; simp [done] at hb
  have hd2 : ∀ a, (done n d2.w).pos a = true → (done n d2.w).neg a = true → False := by
    intro a _ hb; simp [done] at hb
  rw [dadd, daddEq_val n x _ _ (by simp [dmul, done]),
    dmul_val n x d1 (done n d2.w) h1 hd2, dmul_val n x (done n d1.w) d2 hd1 h2,
    done_val, done_val]
  ring

theorem dadd_ok {Q : (Assign → Bool) → Prop} {s W : ℕ} {d1 d2 : GapData} (n : ℕ)
    (k1 : d1.Ok Q s) (k2 : d2.Ok Q s) (hw1 : d1.w ≤ W) (hw2 : d2.w ≤ W) :
    (dadd n d1 d2).Ok Q (32 * (s + 3 * W + 1) + 18) := by
  set s' := s + 3 * W + 1 with hs'
  have k1' : d1.Ok Q s' := k1.mono (by omega)
  have k2' : d2.Ok Q s' := k2.mono (by omega)
  have e1 : (done n d2.w).Ok Q s' := (done_ok n d2.w).mono (by omega)
  have e2 : (done n d1.w).Ok Q s' := (done_ok n d1.w).mono (by omega)
  have m1 := dmul_ok (Q := Q) (s := s') n k1' e1
  have m2 := dmul_ok (Q := Q) (s := s') n e2 k2'
  have := daddEq_ok (Q := Q) (s := 8 * s' + 3) n m1 m2
  exact this.mono (by omega)

theorem dadd_w (n : ℕ) (d1 d2 : GapData) : (dadd n d1 d2).w = d1.w + d2.w + 1 := rfl

/-! #### Balanced products of many gap functions -/

/-- Disjointness of the accepting and rejecting predicates. -/
def Disj (d : GapData) : Prop := ∀ a, d.pos a = true → d.neg a = true → False

theorem dmul_disj (n : ℕ) {d1 d2 : GapData} (h1 : Disj d1) (h2 : Disj d2) :
    Disj (dmul n d1 d2) := by
  intro a hp hn
  simp only [dmul, Bool.or_eq_true, Bool.and_eq_true] at hp hn
  have d1d := h1 (fun i => if i < n then a i else if i < n + d1.w then a (i + 0) else false)
  have d2d := h2 (fun i => if i < n then a i else if i < n + d2.w then a (i + d1.w) else false)
  simp only [view] at hp hn d1d d2d
  rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hn with ⟨hn1, hn2⟩ | ⟨hn1, hn2⟩
  · exact d2d hp2 hn2
  · exact d1d hp1 hn1
  · exact d1d hn1 hp1
  · exact d2d hn2 hp2

/-- The product of the `2 ^ d` gap functions `D off, …, D (off + 2 ^ d - 1)`, computed by a
balanced binary tree (so that the formula size stays polynomial). -/
def dprodTree (n : ℕ) (D : ℕ → GapData) : ℕ → ℕ → GapData
  | 0, off => D off
  | (d + 1), off => dmul n (dprodTree n D d off) (dprodTree n D d (off + 2 ^ d))

theorem dprodTree_disj (n : ℕ) (D : ℕ → GapData) (hD : ∀ i, Disj (D i)) :
    ∀ (d off : ℕ), Disj (dprodTree n D d off)
  | 0, off => hD off
  | (d + 1), off =>
      dmul_disj n (dprodTree_disj n D hD d off) (dprodTree_disj n D hD d (off + 2 ^ d))

theorem dprodTree_val (n : ℕ) (x : Assign) (D : ℕ → GapData) (hD : ∀ i, Disj (D i)) :
    ∀ (d off : ℕ),
      (dprodTree n D d off).val n x = ∏ j ∈ Finset.range (2 ^ d), (D (off + j)).val n x
  | 0, off => by simp [dprodTree]
  | (d + 1), off => by
      rw [dprodTree, dmul_val n x _ _ (dprodTree_disj n D hD d off)
        (dprodTree_disj n D hD d (off + 2 ^ d)),
        dprodTree_val n x D hD d off, dprodTree_val n x D hD d (off + 2 ^ d)]
      have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      rw [h2, Finset.prod_range_add]
      congr 1
      exact Finset.prod_congr rfl fun j _ => by rw [add_assoc]

theorem dprodTree_w (n : ℕ) (D : ℕ → GapData) (w : ℕ) (hw : ∀ i, (D i).w ≤ w) :
    ∀ (d off : ℕ), (dprodTree n D d off).w ≤ 2 ^ d * w
  | 0, off => by simpa [dprodTree] using hw off
  | (d + 1), off => by
      have h1 := dprodTree_w n D w hw d off
      have h2 := dprodTree_w n D w hw d (off + 2 ^ d)
      show (dprodTree n D d off).w + (dprodTree n D d (off + 2 ^ d)).w ≤ _
      have : 2 ^ (d + 1) * w = 2 ^ d * w + 2 ^ d * w := by ring
      omega

theorem dprodTree_ok {Q : (Assign → Bool) → Prop} (n : ℕ) (D : ℕ → GapData) (s : ℕ)
    (hD : ∀ i, (D i).Ok Q s) :
    ∀ (d off : ℕ), (dprodTree n D d off).Ok Q (9 ^ d * (s + 3))
  | 0, off => by simpa [dprodTree] using (hD off).mono (by omega)
  | (d + 1), off => by
      have h1 := dprodTree_ok n D s hD d off
      have h2 := dprodTree_ok n D s hD d (off + 2 ^ d)
      have hmul := dmul_ok (Q := Q) (s := 9 ^ d * (s + 3)) n h1 h2
      refine hmul.mono ?_
      have hp : (1 : ℕ) ≤ 9 ^ d := Nat.one_le_pow _ _ (by omega)
      have he : 9 ^ (d + 1) * (s + 3) = 8 * (9 ^ d * (s + 3)) + 9 ^ d * (s + 3) := by ring
      nlinarith [hp]

end GapData

end CS

/-
Basic framework for a formalization of Toda's theorem.

We work with a semantic notion of "computed by a small formula over a base class `Q`
of oracle predicates".  Inputs are (infinite) Boolean assignments `Assign = ℕ → Bool`;
an input of length `n` only uses the variables `0, …, n-1`, and witnesses are placed in
the variables `n, n+1, …`.
-/
import Mathlib

namespace CS

open scoped BigOperators

/-- An assignment of Boolean values to the variables `0, 1, 2, …`. -/
abbrev Assign := ℕ → Bool

/-! ### Polynomial bounds -/

/-- `s` is bounded by a polynomial. -/
def IsPolyBound (s : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, s n ≤ c * (n + 1) ^ d

theorem IsPolyBound.mono {s t : ℕ → ℕ} (ht : IsPolyBound t) (h : ∀ n, s n ≤ t n) :
    IsPolyBound s := by
  obtain ⟨c, d, hc⟩ := ht
  exact ⟨c, d, fun n => le_trans (h n) (hc n)⟩

theorem isPolyBound_const (c : ℕ) : IsPolyBound (fun _ => c) := by
  refine ⟨c, 0, fun n => ?_⟩
  simp

theorem isPolyBound_id : IsPolyBound (fun n => n) := by
  refine ⟨1, 1, fun n => ?_⟩
  simp

theorem IsPolyBound.add {s t : ℕ → ℕ} (hs : IsPolyBound s) (ht : IsPolyBound t) :
    IsPolyBound (fun n => s n + t n) := by
  obtain ⟨c, d, hc⟩ := hs
  obtain ⟨c', d', hc'⟩ := ht
  refine ⟨c + c', d + d', fun n => ?_⟩
  have h1 : s n ≤ c * (n + 1) ^ (d + d') := by
    refine le_trans (hc n) ?_
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : t n ≤ c' * (n + 1) ^ (d + d') := by
    refine le_trans (hc' n) ?_
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  calc s n + t n ≤ c * (n + 1) ^ (d + d') + c' * (n + 1) ^ (d + d') := by omega
    _ = (c + c') * (n + 1) ^ (d + d') := by ring

theorem IsPolyBound.mul {s t : ℕ → ℕ} (hs : IsPolyBound s) (ht : IsPolyBound t) :
    IsPolyBound (fun n => s n * t n) := by
  obtain ⟨c, d, hc⟩ := hs
  obtain ⟨c', d', hc'⟩ := ht
  refine ⟨c * c', d + d', fun n => ?_⟩
  calc s n * t n ≤ (c * (n + 1) ^ d) * (c' * (n + 1) ^ d') :=
        Nat.mul_le_mul (hc n) (hc' n)
    _ = (c * c') * (n + 1) ^ (d + d') := by ring

theorem IsPolyBound.comp {s t : ℕ → ℕ} (hs : IsPolyBound s) (ht : IsPolyBound t) :
    IsPolyBound (fun n => s (t n)) := by
  obtain ⟨c, d, hc⟩ := hs
  obtain ⟨c', d', hc'⟩ := ht
  refine ⟨c * (c' + 1) ^ d, d' * d, fun n => ?_⟩
  have h1 : t n + 1 ≤ (c' + 1) * (n + 1) ^ d' := by
    have h0 : (1 : ℕ) ≤ (n + 1) ^ d' := Nat.one_le_pow _ _ (by omega)
    have := hc' n
    calc t n + 1 ≤ c' * (n + 1) ^ d' + (n + 1) ^ d' := by omega
      _ = (c' + 1) * (n + 1) ^ d' := by ring
  calc s (t n) ≤ c * (t n + 1) ^ d := hc (t n)
    _ ≤ c * ((c' + 1) * (n + 1) ^ d') ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
    _ = (c * (c' + 1) ^ d) * (n + 1) ^ (d' * d) := by
        rw [Nat.mul_pow, ← pow_mul]; ring

/-! ### Small formulas over a base class -/

/-- `HasFml Q s f` means: the Boolean function `f` of the variables is computed by a
formula of size at most `s` whose leaves are variables, constants, or predicates from the
base class `Q` (thought of as the polynomial-time predicates / oracle gates). -/
inductive HasFml (Q : (Assign → Bool) → Prop) : ℕ → (Assign → Bool) → Prop
  | base {f : Assign → Bool} : Q f → HasFml Q 1 f
  | var (i : ℕ) : HasFml Q 1 (fun a => a i)
  | const (b : Bool) : HasFml Q 1 (fun _ => b)
  | not {s : ℕ} {f : Assign → Bool} : HasFml Q s f → HasFml Q (s + 1) (fun a => !f a)
  | and {s t : ℕ} {f g : Assign → Bool} :
      HasFml Q s f → HasFml Q t g → HasFml Q (s + t + 1) (fun a => f a && g a)
  | or {s t : ℕ} {f g : Assign → Bool} :
      HasFml Q s f → HasFml Q t g → HasFml Q (s + t + 1) (fun a => f a || g a)
  | subst {s t : ℕ} {f : Assign → Bool} {g : ℕ → Assign → Bool} :
      HasFml Q s f → (∀ i, HasFml Q t (g i)) →
      HasFml Q (s * (t + 1)) (fun a => f (fun i => g i a))
  | mono {s t : ℕ} {f : Assign → Bool} : HasFml Q s f → s ≤ t → HasFml Q t f

theorem HasFml.congr' {Q : (Assign → Bool) → Prop} {s : ℕ} {f g : Assign → Bool}
    (h : HasFml Q s f) (hfg : ∀ a, f a = g a) : HasFml Q s g := by
  have : f = g := funext hfg
  exact this ▸ h

/-- Renaming of variables. -/
theorem HasFml.rename {Q : (Assign → Bool) → Prop} {s : ℕ} {f : Assign → Bool}
    (h : HasFml Q s f) (σ : ℕ → ℕ) : HasFml Q (2 * s) (fun a => f (fun i => a (σ i))) := by
  have h2 := HasFml.subst h (t := 1) (g := fun i a => a (σ i)) (fun i => HasFml.var (σ i))
  exact HasFml.mono h2 (by omega)

/-! ### Truncation and extension of assignments -/

/-- Zero out all variables `≥ n`. -/
def trunc (n : ℕ) (x : Assign) : Assign := fun i => if i < n then x i else false

/-- Extend an input of length `n` by a witness `y` of length `w`, placed in the
variables `n, …, n + w - 1`; all further variables are `false`. -/
def ext (n w : ℕ) (x : Assign) (y : Fin w → Bool) : Assign :=
  fun i => if _h : i < n then x i else if h2 : i - n < w then y ⟨i - n, h2⟩ else false

theorem ext_zero (n : ℕ) (x : Assign) (y : Fin 0 → Bool) : ext n 0 x y = trunc n x := by
  funext i
  simp [ext, trunc]

theorem ext_lt {n w : ℕ} {x : Assign} {y : Fin w → Bool} {i : ℕ} (h : i < n) :
    ext n w x y i = x i := by
  simp [ext, h]

theorem ext_ge {n w : ℕ} {x : Assign} {y : Fin w → Bool} {j : ℕ} (h : j < w) :
    ext n w x y (n + j) = y ⟨j, h⟩ := by
  have h1 : ¬ (n + j < n) := by omega
  have h2 : n + j - n = j := by omega
  simp [ext, h1, h2, h]

theorem trunc_ext {n w : ℕ} {x : Assign} {y : Fin w → Bool} :
    ext n w (trunc n x) y = ext n w x y := by
  funext i
  by_cases h : i < n <;> simp [ext, trunc, h]

/-- Appending two witnesses is the same as extending twice. -/
theorem ext_append (n w v : ℕ) (x : Assign) (y : Fin w → Bool) (z : Fin v → Bool) :
    ext n (w + v) x (Fin.append y z) = ext (n + w) v (ext n w x y) z := by
  funext i
  by_cases h : i < n
  · have h' : i < n + w := by omega
    simp [ext, h, h']
  · by_cases h2 : i - n < w
    · have h3 : i < n + w := by omega
      have h4 : i - n < w + v := by omega
      simp only [ext, dif_neg h, dif_pos h4, dif_pos h3]
      have hidx : (⟨i - n, h4⟩ : Fin (w + v)) = Fin.castAdd v ⟨i - n, h2⟩ := by
        apply Fin.ext; simp
      rw [hidx, Fin.append_left, dif_pos h2]
    · by_cases h5 : i - n < w + v
      · have h6 : ¬ (i < n + w) := by omega
        have h7 : i - (n + w) < v := by omega
        simp only [ext, dif_neg h, dif_pos h5, dif_neg h6, dif_pos h7]
        have hidx : (⟨i - n, h5⟩ : Fin (w + v)) = Fin.natAdd w ⟨i - (n + w), h7⟩ := by
          apply Fin.ext; simp; omega
        rw [hidx, Fin.append_right]
      · have h6 : ¬ (i < n + w) := by omega
        have h7 : ¬ (i - (n + w) < v) := by omega
        simp [ext, h, h5, h6, h7]

/-! ### Languages and complexity classes -/

/-- A language: `L n x` says that the length-`n` input `x` (given by the variables
`0, …, n-1`) belongs to the language. -/
def Lang := ℕ → Assign → Prop

/-- The class `P` (relative to the base class `Q`): languages decided by
polynomial-size formulas over `Q`. -/
def InP (Q : (Assign → Bool) → Prop) (L : Lang) : Prop :=
  ∃ (F : ℕ → Assign → Bool) (s : ℕ → ℕ), IsPolyBound s ∧ (∀ n, HasFml Q (s n) (F n)) ∧
    ∀ n x, L n x ↔ F n (trunc n x) = true

/-- The levels `Σₖ` of the polynomial hierarchy. -/
def SigmaC (Q : (Assign → Bool) → Prop) : ℕ → Lang → Prop
  | 0, L => InP Q L
  | (k + 1), L =>
      ∃ (M : Lang) (w : ℕ → ℕ), IsPolyBound w ∧ SigmaC Q k (fun n x => ¬ M n x) ∧
        ∀ n x, L n x ↔ ∃ y : Fin (w n) → Bool, M (n + w n) (ext n (w n) x y)

/-- The polynomial hierarchy. -/
def PH (Q : (Assign → Bool) → Prop) (L : Lang) : Prop := ∃ k, SigmaC Q k L

/-- The number of witnesses of length `w` accepted by `R` on the length-`n` input `x`. -/
def countW (n w : ℕ) (x : Assign) (R : Assign → Bool) : ℕ :=
  (Finset.univ.filter (fun y : Fin w → Bool => R (ext n w x y) = true)).card

/-- The class `#P` (relative to `Q`). -/
def SharpP (Q : (Assign → Bool) → Prop) (f : ℕ → Assign → ℕ) : Prop :=
  ∃ (R : ℕ → Assign → Bool) (w s : ℕ → ℕ), IsPolyBound w ∧ IsPolyBound s ∧
    (∀ n, HasFml Q (s n) (R n)) ∧ ∀ n x, f n x = countW n (w n) x (R n)

/-- Append the binary representation of `v` to the length-`n` input `x`. -/
def appendBits (n : ℕ) (x : Assign) (v : ℕ) : Assign :=
  fun i => if i < n then x i else v.testBit (i - n)

/-- The class `P^{#P}` (relative to `Q`): decided by a polynomial-size formula over `Q`
from the input together with the binary representation of the value of one `#P` function. -/
def PSharpP (Q : (Assign → Bool) → Prop) (L : Lang) : Prop :=
  ∃ f : ℕ → Assign → ℕ, SharpP Q f ∧
    ∃ (G : ℕ → Assign → Bool) (s : ℕ → ℕ), IsPolyBound s ∧ (∀ n, HasFml Q (s n) (G n)) ∧
      ∀ n x, L n x ↔ G n (appendBits n x (f n x)) = true

end CS

