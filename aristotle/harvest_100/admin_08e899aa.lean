import RequestProject.BlumTime

/-!
# The core of the speed-up construction

This file contains the (first-order, oracle-parametrised) combinatorial core of the
diagonal construction used in the proof of Blum's speed-up theorem.

The construction is parametrised by two functions:

* `rf : ℕ → ℕ`, the speed-up factor;
* `T : ℕ → ℕ`, an oracle giving the running time of the (self-referential) code under
  construction at a given input.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Small helpers -/

/-- Bounded universal quantifier, as a `Bool`. -/
def allB (m : ℕ) (p : ℕ → Bool) : Bool := (List.range m).all p

theorem allB_iff {m : ℕ} {p : ℕ → Bool} : allB m p = true ↔ ∀ i < m, p i = true := by
  simp [allB]

theorem le_foldr_max {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    intro h
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The least natural number that does not occur in `V`. -/
def leastNotIn (V : List ℕ) : ℕ :=
  (List.range (V.length + 1)).findIdx (fun v => !V.contains v)

theorem leastNotIn_not_mem (V : List ℕ) : leastNotIn V ∉ V := by
  have hex : ∃ v ∈ List.range (V.length + 1), (!V.contains v) = true := by
    by_contra h
    push_neg at h
    simp only [Bool.not_not_eq, List.contains_iff_mem, List.mem_range] at h
    have hsub : Finset.range (V.length + 1) ⊆ V.toFinset := by
      intro v hv
      simp only [Finset.mem_range] at hv
      simpa using h v hv
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_range] at hcard
    exact absurd (le_trans hcard (List.toFinset_card_le V)) (by omega)
  have h1 : (List.range (V.length + 1)).findIdx (fun v => !V.contains v)
      < (List.range (V.length + 1)).length := List.findIdx_lt_length.2 hex
  have h2 := List.findIdx_getElem (w := h1) (p := fun v => !V.contains v)
    (xs := List.range (V.length + 1))
  rw [List.getElem_range] at h2
  simpa [leastNotIn, List.contains_iff_mem] using h2

/-! ### The construction -/

/-- The largest running time among the members `(i+1, d)` of the family, `d ≤ y`, on input `y`. -/
def maxCost (T : ℕ → ℕ) (i y : ℕ) : ℕ :=
  ((List.range (y + 1)).map fun d => T (Nat.pair (Nat.pair (i + 1) d) y)).foldr max 0

theorem le_maxCost (T : ℕ → ℕ) {i y d : ℕ} (hd : d ≤ y) :
    T (Nat.pair (Nat.pair (i + 1) d) y) ≤ maxCost T i y :=
  le_foldr_max (List.mem_map.2 ⟨d, List.mem_range.2 (Nat.lt_succ_of_le hd), rfl⟩)

theorem foldr_max_le {k : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a ≤ k) → l.foldr max 0 ≤ k := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    intro h
    simp only [List.foldr_cons, max_le_iff]
    exact ⟨h b List.mem_cons_self, ih fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

theorem maxCost_le {T : ℕ → ℕ} {i y k : ℕ}
    (h : ∀ e ≤ y, T (Nat.pair (Nat.pair (i + 1) e) y) ≤ k) : maxCost T i y ≤ k := by
  refine foldr_max_le ?_
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
  exact h e (Nat.lt_succ_iff.1 (List.mem_range.1 he))

theorem maxCost_congr {T T' : ℕ → ℕ} {i y : ℕ}
    (h : ∀ d ≤ y, T (Nat.pair (Nat.pair (i + 1) d) y) = T' (Nat.pair (Nat.pair (i + 1) d) y)) :
    maxCost T i y = maxCost T' i y := by
  unfold maxCost
  congr 1
  refine List.map_congr_left ?_
  intro d hd
  exact h d (Nat.lt_succ_iff.1 (List.mem_range.1 hd))

/-- Index `i` *qualifies* at stage `y` if the code with index `i` halts on `y` within the
threshold `rf (maxCost T i y)`. -/
def qual (rf T : ℕ → ℕ) (i y : ℕ) : Bool :=
  (evaln (rf (maxCost T i y)) (Denumerable.ofNat Code i) y).isSome

/-- Index `i` is *cancelled* at stage `x` if `x` is the first stage after `i` at which `i`
qualifies. -/
def canc (rf T : ℕ → ℕ) (i x : ℕ) : Bool :=
  (decide (i < x) && qual rf T i x) && allB x fun y => decide (y ≤ i) || !qual rf T i y

theorem canc_iff {rf T : ℕ → ℕ} {i x : ℕ} :
    canc rf T i x = true ↔
      i < x ∧ qual rf T i x = true ∧ ∀ y, i < y → y < x → qual rf T i y = false := by
  simp only [canc, Bool.and_eq_true, decide_eq_true_eq, allB_iff, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun y hy hyx => ?_⟩
    rcases h3 y hyx with h | h
    · omega
    · exact h
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun y hyx => if h : y ≤ i then Or.inl h else Or.inr (h3 y (by omega) hyx)⟩

/-- The list of values that must be avoided at stage `x` by the member `n` of the family. -/
def vals (rf T : ℕ → ℕ) (n x : ℕ) : List ℕ :=
  (List.range x).filterMap fun i =>
    bif decide (n ≤ i) && canc rf T i x then
      some ((evaln (rf (maxCost T i x)) (Denumerable.ofNat Code i) x).getD 0)
    else none

theorem mem_vals {rf T : ℕ → ℕ} {n x v : ℕ} :
    v ∈ vals rf T n x ↔ ∃ i < x, n ≤ i ∧ canc rf T i x = true ∧
      v = (evaln (rf (maxCost T i x)) (Denumerable.ofNat Code i) x).getD 0 := by
  simp only [vals, List.mem_filterMap, List.mem_range, Bool.cond_eq_ite]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hc : (decide (n ≤ i) && canc rf T i x) = true
    · rw [if_pos hc] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨i, hi, hc.1, hc.2, (Option.some_inj.1 h).symm⟩
    · rw [if_neg hc] at h; exact absurd h (by simp)
  · rintro ⟨i, hi, hni, hc, rfl⟩
    refine ⟨i, hi, ?_⟩
    rw [if_pos (by simp [hni, hc])]

/-- The value produced at stage `x` by the member `z = (n, d)` of the family: the entry of the
finite table `d` at `x` if there is one, and otherwise the least value avoiding `vals`. -/
def body (rf T : ℕ → ℕ) (z x : ℕ) : ℕ :=
  ((Denumerable.ofNat (List (ℕ × ℕ)) z.unpair.2).lookup x).getD
    (leastNotIn (vals rf T z.unpair.1 x))

/-! ### Congruence -/

/-- The two oracles `(rf, T)` and `(rf', T')` agree on everything that the member `n` of the
family consults at stage `x`. -/
def Agree (rf rf' T T' : ℕ → ℕ) (n x : ℕ) : Prop :=
  ∀ i, n ≤ i → i < x → ∀ y, i < y → y ≤ x →
    (∀ e ≤ y, T (Nat.pair (Nat.pair (i + 1) e) y) = T' (Nat.pair (Nat.pair (i + 1) e) y)) ∧
      rf (maxCost T i y) = rf' (maxCost T' i y)

theorem allB_congr {m : ℕ} {p q : ℕ → Bool} (h : ∀ i < m, p i = q i) : allB m p = allB m q := by
  have key : ∀ l : List ℕ, (∀ i ∈ l, p i = q i) → l.all p = l.all q := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => intro h; simp_all
  exact key _ fun i hi => h i (List.mem_range.1 hi)

theorem qual_congr {rf rf' T T' : ℕ → ℕ} {i y : ℕ}
    (hr : rf (maxCost T i y) = rf' (maxCost T' i y)) : qual rf T i y = qual rf' T' i y := by
  unfold qual
  rw [hr]

theorem canc_congr {rf rf' T T' : ℕ → ℕ} {n i x : ℕ} (h : Agree rf rf' T T' n x)
    (hni : n ≤ i) (hix : i < x) : canc rf T i x = canc rf' T' i x := by
  have hqual : ∀ y, i < y → y ≤ x → qual rf T i y = qual rf' T' i y := by
    intro y hiy hyx
    obtain ⟨-, hr⟩ := h i hni hix y hiy hyx
    exact qual_congr hr
  unfold canc
  rw [hqual x hix le_rfl]
  congr 1
  refine allB_congr ?_
  intro y hy
  rcases lt_or_ge i y with hiy | hiy
  · rw [hqual y hiy (le_of_lt hy)]
  · simp [decide_eq_true (by omega : y ≤ i)]

theorem vals_congr {rf rf' T T' : ℕ → ℕ} {n x : ℕ} (h : Agree rf rf' T T' n x) :
    vals rf T n x = vals rf' T' n x := by
  unfold vals
  refine List.filterMap_congr ?_
  intro i hi
  have hix : i < x := List.mem_range.1 hi
  by_cases hni : n ≤ i
  · obtain ⟨-, hr⟩ := h i hni hix x hix le_rfl
    rw [canc_congr h hni hix, hr]
  · simp [decide_eq_false (by omega : ¬ n ≤ i)]

theorem body_congr {rf rf' T T' : ℕ → ℕ} {n d x : ℕ} (h : Agree rf rf' T T' n x) :
    body rf T (Nat.pair n d) x = body rf' T' (Nat.pair n d) x := by
  unfold body
  simp only [Nat.unpair_pair]
  rw [vals_congr h]

end CS

import Mathlib

/-!
# A running-time measure for `Nat.Partrec.Code`

`Nat.Partrec.Code.evaln k c x` runs the code `c` on input `x` with "fuel" `k`.
We define `CS.time c x` to be the least amount of fuel that suffices, which is a
Blum complexity measure for the programming system `Nat.Partrec.Code`:

* `CS.time c x` is defined exactly when `c` halts on `x`;
* the relation `CS.time c x ≤ k` is decidable (it is `(evaln k c x).isSome`).
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- `Halts c x` means that the code `c` converges on input `x`. -/
def Halts (c : Code) (x : ℕ) : Prop := ∃ k, (evaln k c x).isSome

/-- The running time of the code `c` on input `x`: the least fuel `k` for which
`evaln k c x` succeeds (junk value `0` if `c` diverges on `x`). -/
noncomputable def time (c : Code) (x : ℕ) : ℕ := sInf {k | (evaln k c x).isSome}

theorem halts_iff_dom {c : Code} {x : ℕ} : Halts c x ↔ (eval c x).Dom := by
  constructor
  · rintro ⟨k, hk⟩
    rcases Option.isSome_iff_exists.1 hk with ⟨v, hv⟩
    exact (evaln_sound hv).fst
  · intro h
    obtain ⟨k, hk⟩ := evaln_complete.1 (Part.get_mem h)
    exact ⟨k, Option.isSome_iff_exists.2 ⟨_, hk⟩⟩

theorem time_isSome {c : Code} {x : ℕ} (h : Halts c x) : (evaln (time c x) c x).isSome :=
  Nat.sInf_mem h

theorem time_le {c : Code} {x k : ℕ} (h : (evaln k c x).isSome) : time c x ≤ k :=
  Nat.sInf_le h

theorem isSome_of_time_le {c : Code} {x k : ℕ} (h : Halts c x) (hk : time c x ≤ k) :
    (evaln k c x).isSome := by
  rcases Option.isSome_iff_exists.1 (time_isSome h) with ⟨v, hv⟩
  exact Option.isSome_iff_exists.2 ⟨v, evaln_mono hk hv⟩

theorem not_isSome_iff_lt_time {c : Code} {x k : ℕ} (h : Halts c x) :
    ¬ (evaln k c x).isSome ↔ k < time c x := by
  constructor
  · intro hk
    by_contra hle
    exact hk (isSome_of_time_le h (not_lt.1 hle))
  · intro hk hs
    exact absurd (time_le hs) (not_le.2 hk)

theorem lt_time {c : Code} {x : ℕ} (h : Halts c x) : x < time c x := by
  rcases Option.isSome_iff_exists.1 (time_isSome h) with ⟨v, hv⟩
  exact evaln_bound hv

/-- The value computed, read off from `evaln` at any sufficient fuel. -/
theorem evaln_eq_eval {c : Code} {x k v : ℕ} (h : evaln k c x = some v) :
    eval c x = Part.some v :=
  Part.eq_some_iff.2 (evaln_sound h)

/-! ### Fuel bounds for the standard combinators -/

theorem evaln_const : ∀ (m : ℕ) {k x : ℕ}, x < k → m < k → evaln k (Code.const m) x = some m
  | 0, k + 1, x, hx, _ => by
      simp [Code.const, evaln, Nat.lt_succ_iff.1 hx]
  | m + 1, k + 1, x, hx, hm => by
      have ih := evaln_const m (k := k + 1) hx (by omega)
      simp [Code.const, evaln, ih, Nat.lt_succ_iff.1 hx, Nat.lt_succ_iff.1 (by omega : m < k + 1)]

theorem evaln_id {k x : ℕ} (hx : x < k) : evaln k Code.id x = some x := by
  cases k with
  | zero => omega
  | succ k => simp [Code.id, evaln, Nat.lt_succ_iff.1 hx, Seq.seq]

/-- Currying costs nothing in this measure: any fuel that suffices for `c` on the pair
`(m, x)` also suffices for `curry c m` on `x`. -/
theorem evaln_curry {c : Code} {m x k v : ℕ} (h : evaln k c (Nat.pair m x) = some v) :
    evaln k (curry c m) x = some v := by
  have hb : Nat.pair m x < k := evaln_bound h
  have hx : x < k := lt_of_le_of_lt (Nat.right_le_pair m x) hb
  have hm : m < k := lt_of_le_of_lt (Nat.left_le_pair m x) hb
  cases k with
  | zero => omega
  | succ k =>
    simp [curry, evaln, Nat.lt_succ_iff.1 hx, Seq.seq, evaln_const m hx hm, evaln_id hx, h]

theorem halts_curry {c : Code} {m x : ℕ} (h : Halts c (Nat.pair m x)) : Halts (curry c m) x := by
  obtain ⟨k, hk⟩ := h
  rcases Option.isSome_iff_exists.1 hk with ⟨v, hv⟩
  exact ⟨k, Option.isSome_iff_exists.2 ⟨v, evaln_curry hv⟩⟩

theorem time_curry_le {c : Code} {m x : ℕ} (h : Halts c (Nat.pair m x)) :
    time (curry c m) x ≤ time c (Nat.pair m x) := by
  rcases Option.isSome_iff_exists.1 (time_isSome h) with ⟨v, hv⟩
  exact time_le (Option.isSome_iff_exists.2 ⟨v, evaln_curry hv⟩)

end CS

import RequestProject.BlumPrimrec

/-!
# The self-referential family of programs

Using Kleene's recursion theorem we build a single code `C` such that, for all `n`, `d` and `x`,

`eval C ⟪⟪n, d⟫, x⟫ = body r (time C) ⟪n, d⟫ x`,

i.e. the code computes the diagonal construction of `RequestProject.BlumCore` in which the
thresholds are given in terms of the running times of the code itself.
-/

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The table of values of `r` on `0, …, k`. -/
def rtab (r : ℕ → ℕ) (k : ℕ) : List ℕ := (List.range (k + 1)).map r

theorem rtab_getI {r : ℕ → ℕ} {k v : ℕ} (h : v ≤ k) : (rtab r k).getI v = r v := by
  have hlen : v < (rtab r k).length := by simp [rtab]; omega
  rw [List.getI_eq_getElem _ hlen]
  simp [rtab]

theorem computable_rtab {r : ℕ → ℕ} (hr : Computable r) : Computable (rtab r) := by
  have h : Computable fun k : ℕ =>
      Nat.rec (motive := fun _ => List ℕ) [r 0] (fun n l => l ++ [r (n + 1)]) k := by
    refine Computable.nat_rec (f := fun k : ℕ => k) (g := fun _ : ℕ => [r 0])
      (h := fun (_ : ℕ) (p : ℕ × List ℕ) => p.2 ++ [r (p.1 + 1)]) Computable.id
      (Computable.list_cons.comp (hr.comp (Computable.const 0)) (Computable.const []))
      (Computable₂.mk (Computable.list_append.comp (Computable.snd.comp Computable.snd)
        (Computable.list_cons.comp
          (hr.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))
          (Computable.const []))))
  refine h.of_eq fun k => ?_
  induction k with
  | zero => simp [rtab]
  | succ k ih =>
    simp only [rtab, List.range_succ, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [ih]

/-- The functional whose fixed point is the family of programs. -/
noncomputable def Psi (r : ℕ → ℕ) (C : Code) (w : ℕ) : Part ℕ :=
  (Nat.rfind fun k => Part.some (needB C k w.unpair.1.unpair.1 w.unpair.2)).map fun k =>
    bodyE ((rtab r k, C), k) w.unpair.1 w.unpair.2

theorem partrec_Psi {r : ℕ → ℕ} (hr : Computable r) : Partrec₂ (Psi r) := by
  have hneed : Partrec₂ fun (p : Code × ℕ) (k : ℕ) =>
      (Part.some (needB p.1 k p.2.unpair.1.unpair.1 p.2.unpair.2) : Part Bool) := by
    refine Computable₂.partrec₂ (Computable₂.mk ?_)
    refine (primrec_needB.to_comp).comp
      (g := fun a : (Code × ℕ) × ℕ =>
        (a.1.1, (a.2, (a.1.2.unpair.1.unpair.1, a.1.2.unpair.2)))) ?_
    exact Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair Computable.snd
        (Computable.pair
          (Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp
            (Computable.unpair.comp (Computable.snd.comp Computable.fst)))))
          (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst)))))
  have hbody : Computable₂ fun (p : Code × ℕ) (k : ℕ) =>
      bodyE ((rtab r k, p.1), k) p.2.unpair.1 p.2.unpair.2 := by
    refine Computable₂.mk ((primrec_bodyE.to_comp).comp
      (g := fun a : (Code × ℕ) × ℕ =>
        (((rtab r a.2, a.1.1), a.2), (a.1.2.unpair.1, a.1.2.unpair.2))) ?_)
    refine Computable.pair (Computable.pair
      (Computable.pair ((computable_rtab hr).comp Computable.snd)
        (Computable.fst.comp Computable.fst)) Computable.snd) ?_
    exact Computable.pair
      (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst)))
      (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst)))
  exact Partrec.map (Partrec.rfind hneed) hbody

theorem exists_fixedPoint {r : ℕ → ℕ} (hr : Computable r) : ∃ C : Code, eval C = Psi r C :=
  fixed_point₂ (partrec_Psi hr)

/-! ### Basic facts about the bounded time -/

theorem timeB_eq_time {C : Code} {k z : ℕ} (h : (evaln k C z).isSome) : timeB C k z = time C z := by
  have hhalt : Halts C z := ⟨k, h⟩
  have hle : time C z ≤ k := time_le h
  have hlen : time C z < (List.range (k + 1)).length := by simp; omega
  refine List.findIdx_eq hlen |>.2 ⟨?_, ?_⟩
  · rw [List.getElem_range]
    exact time_isSome hhalt
  · intro j hj
    rw [List.getElem_range]
    have := (not_isSome_iff_lt_time (k := j) hhalt).2 hj
    simpa using this

theorem exists_uniform_fuel {C : Code} (L : List ℕ) (h : ∀ z ∈ L, Halts C z) :
    ∃ k, ∀ z ∈ L, (evaln k C z).isSome := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons z L ih =>
    obtain ⟨k, hk⟩ := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    obtain ⟨k', hk'⟩ := h z List.mem_cons_self
    refine ⟨max k k', fun w hw => ?_⟩
    rcases List.mem_cons.1 hw with rfl | hw
    · exact isSome_of_time_le ⟨k', hk'⟩ (le_trans (time_le hk') (le_max_right _ _))
    · exact isSome_of_time_le ⟨k, hk w hw⟩ (le_trans (time_le (hk w hw)) (le_max_left _ _))

/-- The list of inputs consulted by the member `n` of the family at stage `x`. -/
def needList (n x : ℕ) : List ℕ :=
  ((List.range x).filter fun i => decide (n ≤ i)).flatMap fun i =>
    ((List.range (x + 1)).filter fun y => decide (i < y)).flatMap fun y =>
      (List.range (y + 1)).map fun e => Nat.pair (Nat.pair (i + 1) e) y

theorem mem_needList {n x i y e : ℕ} (hni : n ≤ i) (hix : i < x) (hiy : i < y) (hyx : y ≤ x)
    (hey : e ≤ y) : Nat.pair (Nat.pair (i + 1) e) y ∈ needList n x := by
  simp only [needList, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map,
    decide_eq_true_eq]
  exact ⟨i, ⟨hix, hni⟩, y, ⟨Nat.lt_succ_of_le hyx, hiy⟩, e, Nat.lt_succ_of_le hey, rfl⟩

theorem exists_needB {C : Code} {n x : ℕ}
    (h : ∀ i, n ≤ i → i < x → ∀ y, i < y → y ≤ x → ∀ e ≤ y,
      Halts C (Nat.pair (Nat.pair (i + 1) e) y)) : ∃ k, needB C k n x = true := by
  have hL : ∀ z ∈ needList n x, Halts C z := by
    intro z hz
    simp only [needList, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map,
      decide_eq_true_eq] at hz
    obtain ⟨i, ⟨hix, hni⟩, y, ⟨hy, hiy⟩, e, he, rfl⟩ := hz
    exact h i hni hix y hiy (Nat.lt_succ_iff.1 hy) e (Nat.lt_succ_iff.1 he)
  obtain ⟨k, hk⟩ := exists_uniform_fuel _ hL
  exact ⟨k, needB_iff.2 fun i hni hix y hiy hyx e hey =>
    hk _ (mem_needList hni hix hiy hyx hey)⟩

end CS

import RequestProject.BlumCore

/-!
# Primitive recursiveness of the bounded construction

Here we check that the construction of `RequestProject.BlumCore`, instantiated with a
*bounded* time oracle (`timeB`) and a finite table of values of the speed-up factor,
is primitive recursive in all of its arguments.
-/

set_option maxHeartbeats 1000000

namespace CS

open Primrec Nat.Partrec Nat.Partrec.Code

/-- Bounded running time: the least `k' ≤ k` for which `evaln k' C z` succeeds
(and `k+1` if there is none). -/
def timeB (C : Code) (k z : ℕ) : ℕ := (List.range (k + 1)).findIdx fun k' => (evaln k' C z).isSome

/-- The data the bounded construction depends on: a table of values of the speed-up factor,
the code being defined, and a fuel bound. -/
abbrev Env := (List ℕ × Code) × ℕ

/-- The speed-up factor, read off from the table. -/
def rfE (e : Env) : ℕ → ℕ := fun v => e.1.1.getI v

/-- The bounded time oracle. -/
def costE (e : Env) : ℕ → ℕ := timeB e.1.2 e.2

/-- The bounded instance of `CS.body`. -/
def bodyE (e : Env) (z x : ℕ) : ℕ := body (rfE e) (costE e) z x

/-! ### Primitive recursiveness -/

theorem primrec_decide {α : Type*} [Primcodable α] {p : α → Prop} [DecidablePred p]
    (h : PrimrecPred p) : Primrec fun a => decide (p a) := by
  obtain ⟨_, h⟩ := h
  exact h.of_eq fun a => by congr!

theorem primrec_contains : Primrec₂ (fun (V : List ℕ) (v : ℕ) => V.contains v) := by
  have h : Primrec fun q : List ℕ × ℕ => decide (∃ a ∈ q.1, a = q.2) :=
    primrec_decide (PrimrecRel.exists_mem_list Primrec.eq)
  exact Primrec₂.mk (h.of_eq fun q => by simp)

theorem primrec_leastNotIn : Primrec leastNotIn :=
  Primrec.list_findIdx (f := fun V : List ℕ => List.range (V.length + 1))
    (p := fun V v => !V.contains v)
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))
    (Primrec₂.mk (Primrec.not.comp (primrec_contains.comp Primrec.fst Primrec.snd)))

theorem primrec_allB {α : Type*} [Primcodable α] {f : α → ℕ → Bool} {m : α → ℕ}
    (hm : Primrec m) (hf : Primrec₂ f) : Primrec fun a => allB (m a) (fun y => f a y) := by
  have h : Primrec fun a => ((List.range (m a)).foldr (fun y b => f a y && b) true) :=
    Primrec.list_foldr (f := fun a => List.range (m a)) (g := fun _ => true)
      (h := fun a p => f a p.1 && p.2) (Primrec.list_range.comp hm) (Primrec.const true)
      (Primrec₂.mk (Primrec.and.comp (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)))
  refine h.of_eq fun a => ?_
  simp only [allB]
  induction (List.range (m a)) with
  | nil => simp
  | cons b l ih => simp [ih]

theorem primrec_evalnIsSome : Primrec fun q : (Code × ℕ) × ℕ => (evaln q.1.2 q.1.1 q.2).isSome :=
  Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
      Primrec.snd))

theorem primrec_timeB : Primrec fun p : Code × ℕ × ℕ => timeB p.1 p.2.1 p.2.2 := by
  refine Primrec.list_findIdx (f := fun p : Code × ℕ × ℕ => List.range (p.2.1 + 1))
    (p := fun p k' => (evaln k' p.1 p.2.2).isSome)
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))) ?_
  refine Primrec₂.mk (Primrec.option_isSome.comp ?_)
  exact Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair Primrec.snd (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

theorem primrec_costE : Primrec₂ fun (e : Env) (z : ℕ) => costE e z :=
  Primrec₂.mk (primrec_timeB.comp
    (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)))

theorem primrec_rfE : Primrec₂ fun (e : Env) (v : ℕ) => rfE e v :=
  Primrec₂.mk (Primrec.list_getI.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    Primrec.snd)

theorem primrec_maxCost :
    Primrec fun p : Env × ℕ × ℕ => maxCost (costE p.1) p.2.1 p.2.2 := by
  have hmap : Primrec fun p : Env × ℕ × ℕ =>
      (List.range (p.2.2 + 1)).map
        (fun d => costE p.1 (Nat.pair (Nat.pair (p.2.1 + 1) d) p.2.2)) := by
    refine Primrec.list_map
      (f := fun p : Env × ℕ × ℕ => List.range (p.2.2 + 1))
      (g := fun (p : Env × ℕ × ℕ) (d : ℕ) => costE p.1 (Nat.pair (Nat.pair (p.2.1 + 1) d) p.2.2))
      (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec₂.mk (primrec_costE.comp (Primrec.fst.comp Primrec.fst) ?_))
    exact Primrec₂.natPair.comp
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.list_foldr (f := fun p : Env × ℕ × ℕ =>
      (List.range (p.2.2 + 1)).map (fun d => costE p.1 (Nat.pair (Nat.pair (p.2.1 + 1) d) p.2.2)))
    (g := fun _ => 0) (h := fun _ q => max q.1 q.2) hmap (Primrec.const 0)
    (Primrec₂.mk (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)))

theorem primrec_qual :
    Primrec fun p : Env × ℕ × ℕ => qual (rfE p.1) (costE p.1) p.2.1 p.2.2 := by
  refine Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair
      (f := fun p : Env × ℕ × ℕ => rfE p.1 (maxCost (costE p.1) p.2.1 p.2.2))
      (g := fun p : Env × ℕ × ℕ => Denumerable.ofNat Code p.2.1) ?_ ?_)
      (Primrec.snd.comp Primrec.snd)))
  · exact primrec_rfE.comp Primrec.fst primrec_maxCost
  · exact (Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.snd)

theorem primrec_canc :
    Primrec fun p : Env × ℕ × ℕ => canc (rfE p.1) (costE p.1) p.2.1 p.2.2 := by
  have hq : Primrec₂ fun (p : Env × ℕ × ℕ) (y : ℕ) => qual (rfE p.1) (costE p.1) p.2.1 y :=
    Primrec₂.mk (primrec_qual.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)))
  have hall : Primrec fun p : Env × ℕ × ℕ =>
      allB p.2.2 (fun y => decide (y ≤ p.2.1) || !qual (rfE p.1) (costE p.1) p.2.1 y) := by
    refine primrec_allB (m := fun p : Env × ℕ × ℕ => p.2.2)
      (f := fun (p : Env × ℕ × ℕ) (y : ℕ) =>
        decide (y ≤ p.2.1) || !qual (rfE p.1) (costE p.1) p.2.1 y)
      (Primrec.snd.comp Primrec.snd) (Primrec₂.mk ?_)
    refine Primrec.or.comp ?_ (Primrec.not.comp (hq.comp Primrec.fst Primrec.snd))
    exact primrec_decide
      (Primrec.nat_le.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  refine Primrec.and.comp (Primrec.and.comp ?_ primrec_qual) hall
  exact primrec_decide
    (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem primrec_vals :
    Primrec fun p : Env × ℕ × ℕ => vals (rfE p.1) (costE p.1) p.2.1 p.2.2 := by
  refine Primrec.listFilterMap
    (f := fun p : Env × ℕ × ℕ => List.range p.2.2)
    (g := fun (p : Env × ℕ × ℕ) (i : ℕ) =>
      bif decide (p.2.1 ≤ i) && canc (rfE p.1) (costE p.1) i p.2.2 then
        some ((evaln (rfE p.1 (maxCost (costE p.1) i p.2.2))
          (Denumerable.ofNat Code i) p.2.2).getD 0)
      else none)
    (Primrec.list_range.comp (Primrec.snd.comp Primrec.snd)) (Primrec₂.mk ?_)
  have hcanc : Primrec fun q : (Env × ℕ × ℕ) × ℕ =>
      canc (rfE q.1.1) (costE q.1.1) q.2 q.1.2.2 :=
    primrec_canc.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hcond : Primrec fun q : (Env × ℕ × ℕ) × ℕ =>
      (decide (q.1.2.1 ≤ q.2) && canc (rfE q.1.1) (costE q.1.1) q.2 q.1.2.2) :=
    Primrec.and.comp
      (primrec_decide
        (Primrec.nat_le.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
      hcanc
  have hmax : Primrec fun q : (Env × ℕ × ℕ) × ℕ => maxCost (costE q.1.1) q.2 q.1.2.2 :=
    primrec_maxCost.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hval : Primrec fun q : (Env × ℕ × ℕ) × ℕ =>
      (evaln (rfE q.1.1 (maxCost (costE q.1.1) q.2 q.1.2.2))
        (Denumerable.ofNat Code q.2) q.1.2.2).getD 0 := by
    refine Primrec.option_getD.comp (Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair
        (f := fun q : (Env × ℕ × ℕ) × ℕ => rfE q.1.1 (maxCost (costE q.1.1) q.2 q.1.2.2))
        (g := fun q : (Env × ℕ × ℕ) × ℕ => Denumerable.ofNat Code q.2) ?_ ?_)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) (Primrec.const 0)
    · exact primrec_rfE.comp (Primrec.fst.comp Primrec.fst) hmax
    · exact (Primrec.ofNat Code).comp Primrec.snd
  exact Primrec.cond hcond (Primrec.option_some.comp hval) (Primrec.const none)

theorem primrec_bodyE : Primrec fun p : Env × ℕ × ℕ => bodyE p.1 p.2.1 p.2.2 := by
  have htab : Primrec fun p : Env × ℕ × ℕ =>
      (Denumerable.ofNat (List (ℕ × ℕ)) p.2.1.unpair.2).lookup p.2.2 :=
    Primrec.listLookup.comp (Primrec.snd.comp Primrec.snd)
      ((Primrec.ofNat (List (ℕ × ℕ))).comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))))
  have hels : Primrec fun p : Env × ℕ × ℕ =>
      leastNotIn (vals (rfE p.1) (costE p.1) p.2.1.unpair.1 p.2.2) :=
    primrec_leastNotIn.comp (primrec_vals.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd))))
  exact Primrec.option_getD.comp htab hels

/-- All sub-computations that the member `n` of the family needs at stage `x` have finished
within fuel `k`. -/
def needB (C : Code) (k n x : ℕ) : Bool :=
  allB x fun i => decide (i < n) ||
    allB (x + 1) fun y => decide (y ≤ i) ||
      allB (y + 1) fun d => (evaln k C (Nat.pair (Nat.pair (i + 1) d) y)).isSome

theorem needB_iff {C : Code} {k n x : ℕ} :
    needB C k n x = true ↔
      ∀ i, n ≤ i → i < x → ∀ y, i < y → y ≤ x → ∀ d, d ≤ y →
        (evaln k C (Nat.pair (Nat.pair (i + 1) d) y)).isSome = true := by
  simp only [needB, allB_iff, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h i hni hix y hiy hyx d hdy
    rcases h i hix with h | h
    · omega
    · rcases h y (by omega) with h | h
      · omega
      · exact h d (by omega)
  · intro h i hix
    by_cases hni : i < n
    · exact Or.inl hni
    refine Or.inr fun y hyx => ?_
    by_cases hiy : y ≤ i
    · exact Or.inl hiy
    exact Or.inr fun d hdy => h i (by omega) hix y (by omega) (by omega) d (by omega)

theorem primrec_needB : Primrec fun p : Code × ℕ × ℕ × ℕ => needB p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have h3 : Primrec fun q : (Code × ℕ × ℕ × ℕ) × ℕ × ℕ =>
      allB (q.2.2 + 1)
        (fun d => (evaln q.1.2.1 q.1.1 (Nat.pair (Nat.pair (q.2.1 + 1) d) q.2.2)).isSome) := by
    refine primrec_allB (m := fun q : (Code × ℕ × ℕ × ℕ) × ℕ × ℕ => q.2.2 + 1)
      (f := fun (q : (Code × ℕ × ℕ × ℕ) × ℕ × ℕ) (d : ℕ) =>
        (evaln q.1.2.1 q.1.1 (Nat.pair (Nat.pair (q.2.1 + 1) d) q.2.2)).isSome)
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd))) (Primrec₂.mk ?_)
    refine primrec_evalnIsSome.comp
      (g := fun a : ((Code × ℕ × ℕ × ℕ) × ℕ × ℕ) × ℕ =>
        ((a.1.1.1, a.1.1.2.1), Nat.pair (Nat.pair (a.1.2.1 + 1) a.2) a.1.2.2)) ?_
    refine Primrec.pair (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))) ?_
    exact Primrec₂.natPair.comp
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have h2 : Primrec fun q : (Code × ℕ × ℕ × ℕ) × ℕ =>
      allB (q.1.2.2.2 + 1) (fun y => decide (y ≤ q.2) ||
        allB (y + 1)
          (fun d => (evaln q.1.2.1 q.1.1 (Nat.pair (Nat.pair (q.2 + 1) d) y)).isSome)) := by
    refine primrec_allB (m := fun q : (Code × ℕ × ℕ × ℕ) × ℕ => q.1.2.2.2 + 1)
      (f := fun (q : (Code × ℕ × ℕ × ℕ) × ℕ) (y : ℕ) => decide (y ≤ q.2) ||
        allB (y + 1)
          (fun d => (evaln q.1.2.1 q.1.1 (Nat.pair (Nat.pair (q.2 + 1) d) y)).isSome))
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec₂.mk ?_)
    refine Primrec.or.comp
      (primrec_decide (Primrec.nat_le.comp Primrec.snd (Primrec.snd.comp Primrec.fst))) ?_
    refine h3.comp (g := fun a : ((Code × ℕ × ℕ × ℕ) × ℕ) × ℕ => (a.1.1, (a.1.2, a.2))) ?_
    exact Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  refine primrec_allB (m := fun p : Code × ℕ × ℕ × ℕ => p.2.2.2)
    (f := fun (p : Code × ℕ × ℕ × ℕ) (i : ℕ) => decide (i < p.2.2.1) ||
      allB (p.2.2.2 + 1) (fun y => decide (y ≤ i) ||
        allB (y + 1) (fun d => (evaln p.2.1 p.1 (Nat.pair (Nat.pair (i + 1) d) y)).isSome)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec₂.mk ?_)
  refine Primrec.or.comp
    (primrec_decide (Primrec.nat_lt.comp Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))) ?_
  refine h2.comp (g := fun a : (Code × ℕ × ℕ × ℕ) × ℕ => (a.1, a.2)) ?_
  exact Primrec.pair Primrec.fst Primrec.snd

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

