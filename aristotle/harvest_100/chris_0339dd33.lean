/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

deriving instance DecidableEq for Nat.Partrec.Code

/-! ## Blum complexity measures -/

/-- A *Blum complexity measure* for the standard numbering `Nat.Partrec.Code.eval` of the
partial computable functions.  `cost c x` is the amount of resource used by the program `c`
on input `x`.  Blum's two axioms are:

* `dom_eq`: `cost c x` is defined exactly when the program `c` halts on `x`;
* the graph of `cost` is decidable, witnessed here by a computable `Bool`-valued `graph`. -/
structure BlumMeasure where
  cost : Code → ℕ →. ℕ
  graph : Code → ℕ → ℕ → Bool
  graph_computable : Computable fun p : (Code × ℕ) × ℕ => graph p.1.1 p.1.2 p.2
  graph_spec : ∀ c x m, graph c x m = true ↔ m ∈ cost c x
  dom_eq : ∀ c x, (cost c x).Dom ↔ (c.eval x).Dom

/-! ## The step-counting measure -/

theorem isSome_evaln_mono {c : Code} {x : ℕ} {k₁ k₂ : ℕ} (h : k₁ ≤ k₂)
    (hs : (evaln k₁ c x).isSome = true) : (evaln k₂ c x).isSome = true := by
  rcases Option.isSome_iff_exists.mp hs with ⟨y, hy⟩
  exact Option.isSome_iff_exists.mpr ⟨y, evaln_mono h hy⟩

/-- The graph of the step-counting measure: `m` is the least number of steps sufficient for
`c` to converge on `x`. -/
def stepGraph (c : Code) (x m : ℕ) : Bool :=
  decide ((evaln m c x).isSome = true ∧ (m = 0 ∨ (evaln (m - 1) c x).isSome = false))

/-- The step-counting cost: the least `m` with `evaln m c x` defined. -/
noncomputable def stepCost (c : Code) (x : ℕ) : Part ℕ :=
  ⟨∃ m, (evaln m c x).isSome = true, fun h => Nat.find h⟩

theorem stepGraph_computable :
    Computable fun p : (Code × ℕ) × ℕ => stepGraph p.1.1 p.1.2 p.2 := by
  have h1 : Primrec fun p : (Code × ℕ) × ℕ => evaln p.2 p.1.1 p.1.2 :=
    primrec_evaln.comp (((Primrec.snd).pair (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst))
  have hpred : Primrec fun p : (Code × ℕ) × ℕ => p.2 - 1 := Primrec.pred.comp Primrec.snd
  have h2 : Primrec fun p : (Code × ℕ) × ℕ => evaln (p.2 - 1) p.1.1 p.1.2 :=
    primrec_evaln.comp ((hpred.pair (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst))
  have hs1 : PrimrecPred fun p : (Code × ℕ) × ℕ => (evaln p.2 p.1.1 p.1.2).isSome = true :=
    ⟨fun _ => inferInstance, by simpa using (Primrec.option_isSome.comp h1)⟩
  have hs2 : PrimrecPred fun p : (Code × ℕ) × ℕ =>
      (evaln (p.2 - 1) p.1.1 p.1.2).isSome = false := by
    refine ⟨fun _ => inferInstance, ?_⟩
    refine (Primrec.not.comp (Primrec.option_isSome.comp h2)).of_eq ?_
    intro a; cases h : evaln (a.2 - 1) a.1.1 a.1.2 <;> simp [h]
  have heq : PrimrecPred fun p : (Code × ℕ) × ℕ => p.2 = 0 :=
    Primrec.eq.comp (Primrec.snd) (Primrec.const (0 : ℕ))
  obtain ⟨_, h⟩ := hs1.and (heq.or hs2)
  exact h.to_comp.of_eq (fun p => by simp [stepGraph])

theorem stepGraph_spec (c : Code) (x m : ℕ) : stepGraph c x m = true ↔ m ∈ stepCost c x := by
  simp only [stepGraph, decide_eq_true_eq, stepCost, Part.mem_mk_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨m, h1⟩, ?_⟩
    refine (Nat.find_eq_iff _).mpr ⟨h1, ?_⟩
    intro n hn hns
    rcases h2 with h2 | h2
    · omega
    · exact absurd (isSome_evaln_mono (by omega : n ≤ m - 1) hns) (by simp [h2])
  · rintro ⟨h, hf⟩
    subst hf
    refine ⟨Nat.find_spec h, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
    · exact Or.inl h0
    · right
      have := Nat.find_min h (m := Nat.find h - 1) (by omega)
      simpa using this

theorem stepCost_dom (c : Code) (x : ℕ) : (stepCost c x).Dom ↔ (c.eval x).Dom := by
  show (∃ m, (evaln m c x).isSome = true) ↔ _
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨m, hm⟩
    rcases Option.isSome_iff_exists.mp hm with ⟨y, hy⟩
    exact ⟨y, evaln_sound hy⟩
  · rintro ⟨y, hy⟩
    rcases evaln_complete.mp hy with ⟨k, hk⟩
    exact ⟨k, Option.isSome_iff_exists.mpr ⟨y, hk⟩⟩

/-- The number of steps of Kleene's step-indexed interpreter is a Blum complexity measure. -/
noncomputable def stepMeasure : BlumMeasure where
  cost := stepCost
  graph := stepGraph
  graph_computable := stepGraph_computable
  graph_spec := stepGraph_spec
  dom_eq := stepCost_dom

/-! ## A padding family of programs for the constant zero function -/

/-- An injective, computable family of programs, all computing the constant `0` function. -/
def padCode (n : ℕ) : Code := Code.comp Code.zero (Code.const n)

theorem padCode_primrec : Primrec padCode :=
  primrec₂_comp.comp (Primrec.const Code.zero) primrec_const

theorem eval_padCode (n x : ℕ) : (padCode n).eval x = Part.some 0 := by
  simp [padCode, Code.eval]; rfl

theorem padCode_inj : Function.Injective padCode := by
  intro a b h
  simp only [padCode, Code.comp.injEq, true_and] at h
  exact Nat.Partrec.Code.const_inj h

/-- `padIdx e x` is the index `n ≤ x` with `e = padCode n` if there is one, and a value `> x`
otherwise. -/
def padIdx (e : Code) (x : ℕ) : ℕ := (List.range (x + 1)).findIdx (fun n => padCode n = e)

theorem padIdx_primrec : Primrec fun p : Code × ℕ => padIdx p.1 p.2 := by
  obtain ⟨_, h2⟩ : PrimrecPred (fun p : (Code × ℕ) × ℕ => padCode p.2 = p.1.1) :=
    Primrec.eq.comp (padCode_primrec.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)
  have h2' : Primrec₂ (fun (p : Code × ℕ) (n : ℕ) => decide (padCode n = p.1)) :=
    h2.of_eq (fun p => by simp)
  exact Primrec.list_findIdx (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) h2'

theorem padIdx_pad (n x : ℕ) (h : n ≤ x) : padIdx (padCode n) x = n := by
  unfold padIdx
  rw [List.findIdx_eq (by simp; omega)]
  refine ⟨by simp, ?_⟩
  intro j hj
  simp only [List.getElem_range, decide_eq_false_iff_not]
  exact fun hc => absurd (padCode_inj hc) (by omega)

theorem padIdx_not_pad (e : Code) (h : ∀ n, e ≠ padCode n) (x : ℕ) : ¬padIdx e x ≤ x := by
  have h2 : padIdx e x = (List.range (x + 1)).length := by
    unfold padIdx
    rw [List.findIdx_eq_length]
    intro y _
    simpa using fun hc => (h y) hc.symm
  simp only [List.length_range] at h2
  omega

theorem padIdx_le_imp {e : Code} {x : ℕ} (h : padIdx e x ≤ x) : e = padCode (padIdx e x) := by
  have hlen : padIdx e x < (List.range (x + 1)).length := by simp; omega
  have := List.findIdx_getElem (p := fun n => decide (padCode n = e)) (xs := List.range (x + 1))
    (w := hlen)
  simp only [List.getElem_range, decide_eq_true_eq] at this
  exact this.symm

theorem computable_decide_le : Computable fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by
  obtain ⟨_, h⟩ := (Primrec.nat_le : PrimrecRel fun a b : ℕ => a ≤ b)
  exact h.to_comp.of_eq (fun p => by simp)

theorem computable_decide_eq : Computable fun p : ℕ × ℕ => decide (p.1 = p.2) := by
  obtain ⟨_, h⟩ := (Primrec.eq : PrimrecRel fun a b : ℕ => a = b)
  exact h.to_comp.of_eq (fun p => by simp)

theorem iter_computable {r : ℕ → ℕ} (hr : Computable r) : Computable fun k : ℕ => r^[k] 0 := by
  have h : Computable fun k : ℕ => Nat.rec (motive := fun _ => ℕ) 0 (fun _ ih => r ih) k := by
    refine Computable.nat_rec (f := fun k : ℕ => k) (g := fun _ : ℕ => (0 : ℕ))
      (h := fun _ p => r p.2) Computable.id (Computable.const 0) ?_
    exact hr.comp (Computable.snd.comp Computable.snd)
  refine h.of_eq (fun k => ?_)
  induction k with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ← ih]

end CS

import RequestProject.Base

/-!
# Blum's speedup theorem for an arbitrary Blum complexity measure

This file develops the construction behind Blum's speedup theorem: for *every* Blum complexity
measure and every computable speedup factor `r` there is a computable `f` such that every
program for `f` can be sped up by the factor `r`, almost everywhere, by another program for `f`.
-/

open Nat.Partrec Nat.Partrec.Code Encodable Denumerable

set_option maxHeartbeats 1000000

namespace CS

/-! ## Tools attached to a Blum measure -/

/-- The cost function of a Blum measure is partial computable. -/
theorem cost_partrec (M : BlumMeasure) : Partrec₂ M.cost := by
  have h : Partrec fun p : Code × ℕ => Nat.rfind (fun m => Part.some (M.graph p.1 p.2 m)) := by
    refine Partrec.rfind ?_
    exact (M.graph_computable).of_eq (fun p => rfl)
  refine (h.of_eq (fun p => ?_))
  apply Part.ext
  intro m
  rw [Nat.mem_rfind]
  simp only [Part.mem_some_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact (M.graph_spec _ _ _).mp h1.symm
  · intro hm
    refine ⟨((M.graph_spec _ _ _).mpr hm).symm, ?_⟩
    intro k hk
    by_cases hg : M.graph p.1 p.2 k = true
    · exact absurd (Part.mem_unique ((M.graph_spec _ _ _).mp hg) hm) (by omega)
    · simpa using hg

/-- The decidable test "the cost of `c` on `x` is at most `b`". -/
def costLe (M : BlumMeasure) (c : Code) (x b : ℕ) : Bool :=
  Nat.rec (M.graph c x 0) (fun k ih => ih || M.graph c x (k + 1)) b

theorem costLe_iff (M : BlumMeasure) (c : Code) (x b : ℕ) :
    costLe M c x b = true ↔ ∃ m ≤ b, m ∈ M.cost c x := by
  induction b with
  | zero =>
    simp only [costLe, Nat.le_zero]
    constructor
    · intro h; exact ⟨0, rfl, (M.graph_spec _ _ _).mp h⟩
    · rintro ⟨m, hm, h⟩; subst hm; exact (M.graph_spec _ _ _).mpr h
  | succ k ih =>
    show (costLe M c x k || M.graph c x (k + 1)) = true ↔ _
    rw [Bool.or_eq_true, ih, M.graph_spec]
    constructor
    · rintro (⟨m, hm, h⟩ | h)
      · exact ⟨m, by omega, h⟩
      · exact ⟨k + 1, le_refl _, h⟩
    · rintro ⟨m, hm, h⟩
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact Or.inl ⟨m, by omega, h⟩
      · have hmk : m = k + 1 := by omega
        subst hmk; exact Or.inr h

theorem costLe_computable (M : BlumMeasure) :
    Computable fun p : (Code × ℕ) × ℕ => costLe M p.1.1 p.1.2 p.2 := by
  have harg0 : Computable (fun p : (Code × ℕ) × ℕ => (p.1, 0)) :=
    Computable.fst.pair (Computable.const 0)
  have hg := M.graph_computable.comp harg0
  have arg : Computable (fun p : ((Code × ℕ) × ℕ) × (ℕ × Bool) => (p.1.1, p.2.1 + 1)) :=
    (Computable.fst.comp Computable.fst).pair
      (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
  have h1 := M.graph_computable.comp arg
  have h2 := Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd) h1
  have h3 := Computable.nat_rec (f := fun p : (Code × ℕ) × ℕ => p.2)
    (g := fun p : (Code × ℕ) × ℕ => M.graph p.1.1 p.1.2 0)
    (h := fun (p : (Code × ℕ) × ℕ) (q : ℕ × Bool) => q.2 || M.graph p.1.1 p.1.2 (q.1 + 1))
    Computable.snd hg h2
  exact h3

/-! ## Patched programs -/

/-- The function computed by the program `patchCode C n L`: it follows level `0` of the
construction below the patch length `L`, and level `n` from `L` on. -/
def patchFun (q : Code × ℕ × ℕ) (y : ℕ) : Part ℕ :=
  bif decide (y < q.2.2) then q.1.eval (Nat.pair 0 y) else q.1.eval (Nat.pair q.2.1 y)

theorem patchFun_partrec : Partrec₂ patchFun := by
  have h0 : Computable fun p : (Code × ℕ × ℕ) × ℕ => p.1.1 := Computable.fst.comp Computable.fst
  have hy : Computable fun p : (Code × ℕ × ℕ) × ℕ => p.2 := Computable.snd
  have harg1 := Primrec₂.natPair.to_comp.comp (Computable.const (0 : ℕ)) hy
  have harg2 := Primrec₂.natPair.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst)) hy
  have h1 := eval_part.comp h0 harg1
  have h2 := eval_part.comp h0 harg2
  have hcond : Computable fun p : (Code × ℕ × ℕ) × ℕ => decide (p.2 < p.1.2.2) := by
    obtain ⟨_, hh⟩ : PrimrecPred fun p : (Code × ℕ × ℕ) × ℕ => p.2 < p.1.2.2 :=
      Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact hh.to_comp.of_eq (fun p => by simp)
  exact Partrec.cond hcond h1 h2

theorem patchFun_nat : Partrec₂ fun (a y : ℕ) => patchFun (ofNat (Code × ℕ × ℕ) a) y := by
  have h := patchFun_partrec.comp ((Computable.ofNat (Code × ℕ × ℕ)).comp Computable.fst)
    Computable.snd
  exact h

/-- A code for the universal patched program. -/
noncomputable def patchAux : Code := (exists_code.1 patchFun_nat).choose

theorem patchAux_spec (a y : ℕ) :
    eval patchAux (Nat.pair a y) = patchFun (ofNat (Code × ℕ × ℕ) a) y := by
  have h : eval patchAux = _ := (exists_code.1 patchFun_nat).choose_spec
  rw [h]
  simp [Part.map_id']

/-- The program computing level `n` of the construction, with its first `L` values replaced by
those of level `0`. -/
noncomputable def patchCode (C : Code) (n L : ℕ) : Code := curry patchAux (encode (C, n, L))

theorem eval_patchCode (C : Code) (n L y : ℕ) :
    (patchCode C n L).eval y = patchFun (C, n, L) y := by
  rw [patchCode, eval_curry, patchAux_spec]
  simp

theorem patchCode_primrec : Primrec fun q : Code × ℕ × ℕ => patchCode q.1 q.2.1 q.2.2 := by
  have h := primrec₂_curry.comp (Primrec.const patchAux) (Primrec.encode (α := Code × ℕ × ℕ))
  exact h

attribute [irreducible] patchAux patchCode

/-! ## The construction -/

/-- `maxK M C m u` is the largest cost, over all patch lengths `L ≤ u`, of the patched program
`patchCode C m L` on input `u`. -/
noncomputable def maxK (M : BlumMeasure) (C : Code) (m u : ℕ) : Part ℕ :=
  Nat.rec (M.cost (patchCode C m 0) u)
    (fun L ih => ih.bind fun v => (M.cost (patchCode C m (L + 1)) u).map (fun w => max v w)) u

theorem maxK_partrec (M : BlumMeasure) :
    Partrec fun q : Code × ℕ × ℕ => maxK M q.1 q.2.1 q.2.2 := by
  have hsnd : Computable fun q : Code × ℕ × ℕ => q.2 := Computable.snd
  have hm : Computable fun q : Code × ℕ × ℕ => q.2.1 := Computable.fst.comp hsnd
  have hu : Computable fun q : Code × ℕ × ℕ => q.2.2 := Computable.snd.comp hsnd
  have hC : Computable fun q : Code × ℕ × ℕ => q.1 := Computable.fst
  have hpatch00 := patchCode_primrec.to_comp.comp (hC.pair (hm.pair (Computable.const (0 : ℕ))))
  have hpatch0 : Computable fun q : Code × ℕ × ℕ => patchCode q.1 q.2.1 0 := hpatch00
  have hg0 := (cost_partrec M).comp hpatch0 hu
  have hg : Partrec fun q : Code × ℕ × ℕ => M.cost (patchCode q.1 q.2.1 0) q.2.2 := hg0
  have hfst : Computable fun p : (Code × ℕ × ℕ) × (ℕ × ℕ) => p.1 := Computable.fst
  have hsnd2 : Computable fun p : (Code × ℕ × ℕ) × (ℕ × ℕ) => p.2 := Computable.snd
  have hC2 := hC.comp hfst
  have hm2 := hm.comp hfst
  have hu2 := hu.comp hfst
  have hj := (Computable.fst : Computable fun s : ℕ × ℕ => s.1).comp hsnd2
  have hv := (Computable.snd : Computable fun s : ℕ × ℕ => s.2).comp hsnd2
  have hpatchS := patchCode_primrec.to_comp.comp
    (hC2.pair (hm2.pair (Primrec.succ.to_comp.comp hj)))
  have hcostS0 := (cost_partrec M).comp hpatchS hu2
  have hcostS : Partrec fun p : (Code × ℕ × ℕ) × (ℕ × ℕ) =>
      M.cost (patchCode p.1.1 p.1.2.1 (p.2.1 + 1)) p.1.2.2 := hcostS0
  have hmax0 := Primrec.nat_max.to_comp.comp
    (hv.comp (Computable.fst : Computable fun z : ((Code × ℕ × ℕ) × (ℕ × ℕ)) × ℕ => z.1))
    (Computable.snd : Computable fun z : ((Code × ℕ × ℕ) × (ℕ × ℕ)) × ℕ => z.2)
  have hmax : Computable₂ fun (p : (Code × ℕ × ℕ) × (ℕ × ℕ)) (w : ℕ) => max p.2.2 w := hmax0
  have hh := Partrec.map hcostS hmax
  have h := Partrec.nat_rec (f := fun q : Code × ℕ × ℕ => q.2.2)
    (g := fun q : Code × ℕ × ℕ => M.cost (patchCode q.1 q.2.1 0) q.2.2)
    (h := fun (q : Code × ℕ × ℕ) (p : ℕ × ℕ) =>
      (M.cost (patchCode q.1 q.2.1 (p.1 + 1)) q.2.2).map (fun w => max p.2 w))
    hu hg hh
  exact h

/-- The bound used at stage `u` for the index `i`: `r` applied to the largest cost of a
patched level-`(i+1)` program at `u`. -/
noncomputable def bound (M : BlumMeasure) (r : ℕ → ℕ) (C : Code) (i u : ℕ) : Part ℕ :=
  (maxK M C (i + 1) u).map r

theorem bound_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ => bound M r q.1 q.2.1 q.2.2 := by
  have hC : Computable fun q : Code × ℕ × ℕ => q.1 := Computable.fst
  have hi : Computable fun q : Code × ℕ × ℕ => q.2.1 :=
    Computable.fst.comp (Computable.snd : Computable fun q : Code × ℕ × ℕ => q.2)
  have hu : Computable fun q : Code × ℕ × ℕ => q.2.2 :=
    Computable.snd.comp (Computable.snd : Computable fun q : Code × ℕ × ℕ => q.2)
  have harg0 := hC.pair ((Primrec.succ.to_comp.comp hi).pair hu)
  have harg : Computable fun q : Code × ℕ × ℕ => (q.1, q.2.1 + 1, q.2.2) := harg0
  have hmk0 := (maxK_partrec M).comp harg
  have hmk : Partrec fun q : Code × ℕ × ℕ => maxK M q.1 (q.2.1 + 1) q.2.2 := hmk0
  have hr2 : Computable₂ fun (_ : Code × ℕ × ℕ) (v : ℕ) => r v := hr.comp Computable.snd
  have h := Partrec.map hmk hr2
  exact h

/-! ## Eligibility and cancellation -/

/-- Index `i` is *eligible* at stage `y` if the cost of program `i` on input `y` is at most the
bound attached to `i` at that stage. -/
noncomputable def elig (M : BlumMeasure) (r : ℕ → ℕ) (C : Code) (i y : ℕ) : Part Bool :=
  (bound M r C i y).map fun b => costLe M (ofNat Code i) y b

/-- `noElig M r C i x` is true iff `i` is not eligible at any stage `y` with `i ≤ y < x`. -/
noncomputable def noElig (M : BlumMeasure) (r : ℕ → ℕ) (C : Code) (i x : ℕ) : Part Bool :=
  Nat.rec (Part.some true)
    (fun y ih => ih.bind fun t =>
      bif decide (y < i) then Part.some t else (elig M r C i y).map fun e => t && !e) x

/-- Index `i` is *cancelled* at stage `x` if `i ≤ x`, `i` is eligible at `x`, and `i` was not
eligible at any earlier stage `y` with `i ≤ y < x`. -/
noncomputable def cancelAt (M : BlumMeasure) (r : ℕ → ℕ) (C : Code) (i x : ℕ) : Part Bool :=
  bif decide (i ≤ x) then
      (elig M r C i x).bind (fun e => (noElig M r C i x).map fun t => e && t)
    else Part.some false

/-- The contribution of index `i` to the value of level `n` at stage `x`. -/
noncomputable def contrib (M : BlumMeasure) (r : ℕ → ℕ) (C : Code) (n x i : ℕ) : Part ℕ :=
  bif decide (n ≤ i) then
      (cancelAt M r C i x).bind (fun b =>
        bif b then ((ofNat Code i).eval x).map (· + 1) else Part.some 0)
    else Part.some 0

/-- The value of level `n` at stage `x`: one more than the largest value `φ_i(x)` over all
indices `i ∈ [n, x]` cancelled at stage `x` (and `0` if there are none). -/
noncomputable def acc (M : BlumMeasure) (r : ℕ → ℕ) (C : Code) (n x : ℕ) : Part ℕ :=
  Nat.rec (contrib M r C n x 0)
    (fun k ih => ih.bind fun v => (contrib M r C n x (k + 1)).map fun w => max v w) x

/-- The whole family of levels, packed into a single partial function. -/
noncomputable def bigF (M : BlumMeasure) (r : ℕ → ℕ) (C : Code) : ℕ →. ℕ :=
  fun a => acc M r C a.unpair.1 a.unpair.2

theorem elig_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ => elig M r q.1 q.2.1 q.2.2 := by
  have hb := bound_partrec M hr
  have hi : Computable fun p : (Code × ℕ × ℕ) × ℕ => (ofNat Code p.1.2.1) :=
    (Computable.ofNat Code).comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hy : Computable fun p : (Code × ℕ × ℕ) × ℕ => p.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hcl0 := (costLe_computable M).comp ((hi.pair hy).pair Computable.snd)
  have hcl : Computable₂ fun (q : Code × ℕ × ℕ) (b : ℕ) =>
      costLe M (ofNat Code q.2.1) q.2.2 b := hcl0
  have h := Partrec.map hb hcl
  exact h

theorem noElig_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ => noElig M r q.1 q.2.1 q.2.2 := by
  have hx : Computable fun q : Code × ℕ × ℕ => q.2.2 :=
    Computable.snd.comp Computable.snd
  have hg : Partrec fun _ : Code × ℕ × ℕ => (Part.some true) := Computable.const true
  have hcond : Computable fun p : (Code × ℕ × ℕ) × (ℕ × Bool) =>
      decide (p.2.1 < p.1.2.1) := by
    obtain ⟨_, hh⟩ : PrimrecPred fun p : (Code × ℕ × ℕ) × (ℕ × Bool) => p.2.1 < p.1.2.1 :=
      Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    exact hh.to_comp.of_eq (fun p => by simp)
  have hbr1 : Partrec fun p : (Code × ℕ × ℕ) × (ℕ × Bool) => (Part.some p.2.2) :=
    Computable.snd.comp Computable.snd
  have harg : Computable fun p : (Code × ℕ × ℕ) × (ℕ × Bool) => (p.1.1, p.1.2.1, p.2.1) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.fst.comp Computable.snd))
  have helig := (elig_partrec M hr).comp harg
  have hmap : Computable₂ fun (p : (Code × ℕ × ℕ) × (ℕ × Bool)) (e : Bool) => p.2.2 && !e :=
    Primrec.and.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
      (Primrec.not.to_comp.comp Computable.snd)
  have hbr2 := Partrec.map helig hmap
  have hh := Partrec.cond hcond hbr1 hbr2
  have h := Partrec.nat_rec (f := fun q : Code × ℕ × ℕ => q.2.2)
    (g := fun _ : Code × ℕ × ℕ => (Part.some true))
    (h := fun (q : Code × ℕ × ℕ) (p : ℕ × Bool) =>
      bif decide (p.1 < q.2.1) then Part.some p.2
        else (elig M r q.1 q.2.1 p.1).map fun e => p.2 && !e)
    hx hg hh
  exact h

theorem cancelAt_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ => cancelAt M r q.1 q.2.1 q.2.2 := by
  have hcond : Computable fun q : Code × ℕ × ℕ => decide (q.2.1 ≤ q.2.2) := by
    obtain ⟨_, hh⟩ : PrimrecPred fun q : Code × ℕ × ℕ => q.2.1 ≤ q.2.2 :=
      Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    exact hh.to_comp.of_eq (fun p => by simp)
  have helig := elig_partrec M hr
  have hno := (noElig_partrec M hr).comp
    (Computable.fst : Computable fun p : (Code × ℕ × ℕ) × Bool => p.1)
  have hmap : Computable₂ fun (p : (Code × ℕ × ℕ) × Bool) (t : Bool) => p.2 && t :=
    Primrec.and.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd
  have hbody := Partrec.map hno hmap
  have hthen := Partrec.bind helig hbody.to₂
  have helse : Partrec fun _ : Code × ℕ × ℕ => (Part.some false) := Computable.const false
  have h := Partrec.cond hcond hthen helse
  exact h

theorem contrib_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ × ℕ => contrib M r q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hcond : Computable fun q : Code × ℕ × ℕ × ℕ => decide (q.2.1 ≤ q.2.2.2) := by
    obtain ⟨_, hh⟩ : PrimrecPred fun q : Code × ℕ × ℕ × ℕ => q.2.1 ≤ q.2.2.2 :=
      Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact hh.to_comp.of_eq (fun p => by simp)
  have harg : Computable fun q : Code × ℕ × ℕ × ℕ => (q.1, q.2.2.2, q.2.2.1) :=
    Computable.fst.pair
      ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hcanc := (cancelAt_partrec M hr).comp harg
  have hb : Computable fun p : (Code × ℕ × ℕ × ℕ) × Bool => p.2 := Computable.snd
  have hcode : Computable fun p : (Code × ℕ × ℕ × ℕ) × Bool => ofNat Code p.1.2.2.2 :=
    (Computable.ofNat Code).comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hx : Computable fun p : (Code × ℕ × ℕ × ℕ) × Bool => p.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hev := eval_part.comp hcode hx
  have hsucc : Computable₂ fun (_ : (Code × ℕ × ℕ × ℕ) × Bool) (v : ℕ) => v + 1 :=
    Primrec.succ.to_comp.comp Computable.snd
  have hthen1 := Partrec.map hev hsucc
  have helse1 : Partrec fun _ : (Code × ℕ × ℕ × ℕ) × Bool => (Part.some 0) :=
    Computable.const 0
  have hinner := Partrec.cond hb hthen1 helse1
  have hthen := Partrec.bind hcanc hinner.to₂
  have helse : Partrec fun _ : Code × ℕ × ℕ × ℕ => (Part.some 0) := Computable.const 0
  have h := Partrec.cond hcond hthen helse
  exact h

theorem acc_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ => acc M r q.1 q.2.1 q.2.2 := by
  have hx : Computable fun q : Code × ℕ × ℕ => q.2.2 := Computable.snd.comp Computable.snd
  have harg0 : Computable fun q : Code × ℕ × ℕ => (q.1, q.2.1, q.2.2, (0:ℕ)) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      ((Computable.snd.comp Computable.snd).pair (Computable.const 0)))
  have hg := (contrib_partrec M hr).comp harg0
  have hargS : Computable fun p : (Code × ℕ × ℕ) × (ℕ × ℕ) =>
      (p.1.1, p.1.2.1, p.1.2.2, p.2.1 + 1) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
          (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))))
  have hcS := (contrib_partrec M hr).comp hargS
  have hmax : Computable₂ fun (p : (Code × ℕ × ℕ) × (ℕ × ℕ)) (w : ℕ) => max p.2.2 w :=
    Primrec.nat_max.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
      Computable.snd
  have hh := Partrec.map hcS hmax
  have h := Partrec.nat_rec (f := fun q : Code × ℕ × ℕ => q.2.2)
    (g := fun q : Code × ℕ × ℕ => contrib M r q.1 q.2.1 q.2.2 0)
    (h := fun (q : Code × ℕ × ℕ) (p : ℕ × ℕ) =>
      (contrib M r q.1 q.2.1 q.2.2 (p.1 + 1)).map fun w => max p.2 w)
    hx hg hh
  exact h

theorem bigF_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec₂ fun (C : Code) (a : ℕ) => bigF M r C a := by
  have harg : Computable fun p : Code × ℕ => (p.1, p.2.unpair.1, p.2.unpair.2) :=
    Computable.fst.pair
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp.pair
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
  have h := (acc_partrec M hr).comp harg
  exact h

/-! ## Elementary facts about the construction -/

section Facts

variable {M : BlumMeasure} {r : ℕ → ℕ} {C : Code}

theorem maxK_dom (m u : ℕ) (h : ∀ L ≤ u, (M.cost (patchCode C m L) u).Dom) :
    (maxK M C m u).Dom := by
  have key : ∀ j ≤ u, ∃ v : ℕ, v ∈ (Nat.rec (motive := fun _ => Part ℕ)
      (M.cost (patchCode C m 0) u)
      (fun L ih => ih.bind fun v => (M.cost (patchCode C m (L+1)) u).map (fun w => max v w))
      j) := by
    intro j
    induction j with
    | zero => intro _; exact Part.dom_iff_mem.mp (h 0 (Nat.zero_le u))
    | succ k ih =>
      intro hk
      obtain ⟨v, hv⟩ := ih (by omega)
      obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp (h (k+1) hk)
      exact ⟨max v w, by simp only [Part.mem_bind_iff, Part.mem_map_iff]; exact ⟨v, hv, w, hw, rfl⟩⟩
  exact Part.dom_iff_mem.mpr (key u le_rfl)

theorem maxK_ge (m u L : ℕ) (hL : L ≤ u) {K : ℕ} (hK : K ∈ maxK M C m u)
    {c : ℕ} (hc : c ∈ M.cost (patchCode C m L) u) : c ≤ K := by
  have key : ∀ j, ∀ K ∈ (Nat.rec (motive := fun _ => Part ℕ)
      (M.cost (patchCode C m 0) u)
      (fun L ih => ih.bind fun v => (M.cost (patchCode C m (L+1)) u).map (fun w => max v w))
      j), L ≤ j → c ≤ K := by
    intro j
    induction j with
    | zero =>
      intro K hK hLj
      have hL0 : L = 0 := by omega
      subst hL0
      exact le_of_eq (Part.mem_unique hc hK)
    | succ k ih =>
      intro K hK hLj
      simp only [Part.mem_bind_iff, Part.mem_map_iff] at hK
      obtain ⟨v, hv, w, hw, rfl⟩ := hK
      rcases Nat.lt_or_ge L (k+1) with hlt | hge
      · exact le_trans (ih v hv (by omega)) (le_max_left _ _)
      · have hLk : L = k + 1 := by omega
        subst hLk
        exact le_trans (le_of_eq (Part.mem_unique hc hw)) (le_max_right _ _)
  exact key u K hK hL

theorem acc_dom_of {n x : ℕ} (h : ∀ i ≤ x, (contrib M r C n x i).Dom) :
    (acc M r C n x).Dom := by
  have key : ∀ j ≤ x, ∃ v : ℕ, v ∈ (Nat.rec (motive := fun _ => Part ℕ)
      (contrib M r C n x 0)
      (fun k ih => ih.bind fun v => (contrib M r C n x (k+1)).map fun w => max v w) j) := by
    intro j
    induction j with
    | zero => intro _; exact Part.dom_iff_mem.mp (h 0 (Nat.zero_le x))
    | succ k ih =>
      intro hk
      obtain ⟨v, hv⟩ := ih (by omega)
      obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp (h (k+1) hk)
      exact ⟨max v w, by simp only [Part.mem_bind_iff, Part.mem_map_iff]; exact ⟨v, hv, w, hw, rfl⟩⟩
  exact Part.dom_iff_mem.mpr (key x le_rfl)

theorem acc_ge_contrib {n x i : ℕ} (hi : i ≤ x) {v : ℕ} (hv : v ∈ acc M r C n x)
    {c : ℕ} (hc : c ∈ contrib M r C n x i) : c ≤ v := by
  have key : ∀ j, ∀ v ∈ (Nat.rec (motive := fun _ => Part ℕ)
      (contrib M r C n x 0)
      (fun k ih => ih.bind fun v => (contrib M r C n x (k+1)).map fun w => max v w) j),
      i ≤ j → c ≤ v := by
    intro j
    induction j with
    | zero =>
      intro v hv hij
      have hi0 : i = 0 := by omega
      subst hi0
      exact le_of_eq (Part.mem_unique hc hv)
    | succ k ih =>
      intro V hV hij
      simp only [Part.mem_bind_iff, Part.mem_map_iff] at hV
      obtain ⟨v, hv, w, hw, rfl⟩ := hV
      rcases Nat.lt_or_ge i (k+1) with hlt | hge
      · exact le_trans (ih v hv (by omega)) (le_max_left _ _)
      · have hik : i = k + 1 := by omega
        subst hik
        exact le_trans (le_of_eq (Part.mem_unique hc hw)) (le_max_right _ _)
  exact key x v hv hi

theorem acc_congr {n m x : ℕ} (h : ∀ i ≤ x, contrib M r C n x i = contrib M r C m x i) :
    acc M r C n x = acc M r C m x := by
  have key : ∀ j ≤ x, (Nat.rec (motive := fun _ => Part ℕ)
      (contrib M r C n x 0)
      (fun k ih => ih.bind fun v => (contrib M r C n x (k+1)).map fun w => max v w) j)
      = (Nat.rec (motive := fun _ => Part ℕ)
      (contrib M r C m x 0)
      (fun k ih => ih.bind fun v => (contrib M r C m x (k+1)).map fun w => max v w) j) := by
    intro j
    induction j with
    | zero => intro _; exact h 0 (Nat.zero_le x)
    | succ k ih =>
      intro hk
      show Part.bind _ _ = Part.bind _ _
      rw [ih (by omega), h (k+1) hk]
  exact key x le_rfl

theorem noElig_succ (i x : ℕ) : noElig M r C i (x+1) =
    (noElig M r C i x).bind fun t =>
      bif decide (x < i) then Part.some t else (elig M r C i x).map fun e => t && !e := rfl

theorem noElig_dom_of {i x : ℕ} (h : ∀ y, i ≤ y → y < x → (elig M r C i y).Dom) :
    (noElig M r C i x).Dom := by
  induction x with
  | zero => exact trivial
  | succ k ih =>
    have hk := ih (fun y hy hyk => h y hy (by omega))
    obtain ⟨t, ht⟩ := Part.dom_iff_mem.mp hk
    rw [noElig_succ]
    rcases Nat.lt_or_ge k i with hlt | hge
    · refine Part.dom_iff_mem.mpr ⟨t, ?_⟩
      simp only [Part.mem_bind_iff]
      exact ⟨t, ht, by simp [hlt]⟩
    · obtain ⟨e, he⟩ := Part.dom_iff_mem.mp (h k hge (by omega))
      refine Part.dom_iff_mem.mpr ⟨t && !e, ?_⟩
      simp only [Part.mem_bind_iff]
      refine ⟨t, ht, ?_⟩
      rw [(by simp; omega : decide (k < i) = false)]
      simp only [cond_false, Part.mem_map_iff]
      exact ⟨e, he, rfl⟩

theorem noElig_spec {i x : ℕ} (h : true ∈ noElig M r C i x) :
    ∀ y, i ≤ y → y < x → false ∈ elig M r C i y := by
  induction x with
  | zero => intro y _ hy; omega
  | succ k ih =>
    rw [noElig_succ] at h
    simp only [Part.mem_bind_iff] at h
    obtain ⟨t, ht, hb⟩ := h
    rcases Nat.lt_or_ge k i with hlt | hge
    · rw [(by simp [hlt] : decide (k < i) = true)] at hb
      simp only [cond_true, Part.mem_some_iff] at hb
      subst hb
      intro y hy hyk
      exact ih ht y hy (by omega)
    · rw [(by simp; omega : decide (k < i) = false)] at hb
      simp only [cond_false, Part.mem_map_iff] at hb
      obtain ⟨e, he, heq⟩ := hb
      have ht' : t = true := by cases t <;> simp_all
      have he' : e = false := by cases e <;> simp_all
      subst ht'; subst he'
      intro y hy hyk
      rcases Nat.lt_or_ge y k with hlt2 | hge2
      · exact ih ht y hy hlt2
      · have hyk' : y = k := by omega
        subst hyk'
        exact he

theorem noElig_of {i x : ℕ} (h : ∀ y, i ≤ y → y < x → false ∈ elig M r C i y) :
    true ∈ noElig M r C i x := by
  induction x with
  | zero => exact Part.mem_some _
  | succ k ih =>
    have ht := ih (fun y hy hyk => h y hy (by omega))
    rw [noElig_succ]
    simp only [Part.mem_bind_iff]
    refine ⟨true, ht, ?_⟩
    rcases Nat.lt_or_ge k i with hlt | hge
    · rw [(by simp [hlt] : decide (k < i) = true)]
      exact Part.mem_some _
    · rw [(by simp; omega : decide (k < i) = false)]
      simp only [cond_false, Part.mem_map_iff]
      exact ⟨false, h k hge (by omega), rfl⟩

theorem elig_mem_iff {i y : ℕ} {e : Bool} :
    e ∈ elig M r C i y ↔ ∃ K ∈ maxK M C (i+1) y, e = costLe M (ofNat Code i) y (r K) := by
  simp only [elig, bound, Part.mem_map_iff]
  constructor
  · rintro ⟨b, ⟨K, hK, rfl⟩, rfl⟩
    exact ⟨K, hK, rfl⟩
  · rintro ⟨K, hK, rfl⟩
    exact ⟨r K, ⟨K, hK, rfl⟩, rfl⟩

theorem elig_dom_of {i y : ℕ} (h : (maxK M C (i+1) y).Dom) : (elig M r C i y).Dom := by
  obtain ⟨K, hK⟩ := Part.dom_iff_mem.mp h
  exact Part.dom_iff_mem.mpr ⟨_, elig_mem_iff.mpr ⟨K, hK, rfl⟩⟩

theorem cost_dom_of_elig {i y : ℕ} (h : true ∈ elig M r C i y) :
    (M.cost (ofNat Code i) y).Dom := by
  obtain ⟨K, hK, hcl⟩ := elig_mem_iff.mp h
  obtain ⟨m, -, hmem⟩ := (costLe_iff M (ofNat Code i) y (r K)).mp hcl.symm
  exact Part.dom_iff_mem.mpr ⟨m, hmem⟩

theorem cost_gt_of_not_elig {i y : ℕ} (h : false ∈ elig M r C i y) {c : ℕ}
    (hc : c ∈ M.cost (ofNat Code i) y) : ∃ K ∈ maxK M C (i+1) y, r K < c := by
  obtain ⟨K, hK, hcl⟩ := elig_mem_iff.mp h
  refine ⟨K, hK, ?_⟩
  by_contra hcon
  have hct : costLe M (ofNat Code i) y (r K) = true :=
    (costLe_iff M (ofNat Code i) y (r K)).mpr ⟨c, by omega, hc⟩
  rw [← hcl] at hct
  exact Bool.false_ne_true hct

theorem cancelAt_mem_true_iff {i x : ℕ} :
    true ∈ cancelAt M r C i x ↔
      i ≤ x ∧ true ∈ elig M r C i x ∧ true ∈ noElig M r C i x := by
  unfold cancelAt
  by_cases hix : i ≤ x
  · rw [(by simp [hix] : decide (i ≤ x) = true)]
    simp only [cond_true, Part.mem_bind_iff, Part.mem_map_iff]
    constructor
    · rintro ⟨e, he, t, ht, hand⟩
      have he' : e = true := by cases e <;> simp_all
      have ht' : t = true := by cases t <;> simp_all
      subst he'; subst ht'
      exact ⟨hix, he, ht⟩
    · rintro ⟨-, he, ht⟩
      exact ⟨true, he, true, ht, rfl⟩
  · rw [(by simp [hix] : decide (i ≤ x) = false)]
    simp only [cond_false, Part.mem_some_iff]
    constructor
    · intro h; exact absurd h.symm Bool.false_ne_true
    · rintro ⟨h, -⟩; exact absurd h hix

theorem cancelAt_dom_of {i x : ℕ} (h1 : (elig M r C i x).Dom) (h2 : (noElig M r C i x).Dom) :
    (cancelAt M r C i x).Dom := by
  unfold cancelAt
  by_cases hix : i ≤ x
  · rw [(by simp [hix] : decide (i ≤ x) = true)]
    obtain ⟨e, he⟩ := Part.dom_iff_mem.mp h1
    obtain ⟨t, ht⟩ := Part.dom_iff_mem.mp h2
    exact Part.dom_iff_mem.mpr ⟨e && t, by
      simp only [cond_true, Part.mem_bind_iff, Part.mem_map_iff]
      exact ⟨e, he, t, ht, rfl⟩⟩
  · rw [(by simp [hix] : decide (i ≤ x) = false)]
    exact trivial

theorem contrib_of_lt {n x i : ℕ} (h : ¬ n ≤ i) : contrib M r C n x i = Part.some 0 := by
  unfold contrib
  rw [(by simp [h] : decide (n ≤ i) = false)]
  rfl

theorem contrib_eq_of_not_cancel {n x i : ℕ} (hc : false ∈ cancelAt M r C i x) :
    contrib M r C n x i = Part.some 0 := by
  unfold contrib
  by_cases h : n ≤ i
  · rw [(by simp [h] : decide (n ≤ i) = true), Part.eq_some_iff.mpr hc]
    simp
  · rw [(by simp [h] : decide (n ≤ i) = false)]
    rfl

theorem contrib_mem_of_cancel {n x i w : ℕ} (hn : n ≤ i) (hc : true ∈ cancelAt M r C i x)
    (hw : w ∈ (ofNat Code i).eval x) : (w + 1) ∈ contrib M r C n x i := by
  unfold contrib
  rw [(by simp [hn] : decide (n ≤ i) = true), Part.eq_some_iff.mpr hc]
  simp only [cond_true, Part.bind_some, Part.mem_map_iff]
  exact ⟨w, hw, rfl⟩

theorem contrib_dom_of {n x i : ℕ} (h : (cancelAt M r C i x).Dom)
    (hev : true ∈ cancelAt M r C i x → ((ofNat Code i).eval x).Dom) :
    (contrib M r C n x i).Dom := by
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
  cases b with
  | false => rw [contrib_eq_of_not_cancel hb]; trivial
  | true =>
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp (hev hb)
    by_cases hn : n ≤ i
    · exact Part.dom_iff_mem.mpr ⟨w + 1, contrib_mem_of_cancel hn hb hw⟩
    · rw [contrib_of_lt hn]; trivial

theorem contrib_eq_contrib_of_iff {n m x i : ℕ} (h : (n ≤ i) ↔ (m ≤ i)) :
    contrib M r C n x i = contrib M r C m x i := by
  unfold contrib
  rw [(by simp [h] : decide (n ≤ i) = decide (m ≤ i))]

end Facts

/-! ## The self-referential family of levels -/

section SelfRef

variable (M : BlumMeasure) {r : ℕ → ℕ}

/-- A code for the whole family of levels, obtained from the recursion theorem, so that it can
refer to itself. -/
noncomputable def selfCode (hr : Computable r) : Code :=
  (fixed_point₂ (bigF_partrec M hr)).choose

theorem eval_selfCode (hr : Computable r) :
    eval (selfCode M hr) = bigF M r (selfCode M hr) :=
  (fixed_point₂ (bigF_partrec M hr)).choose_spec

theorem eval_selfCode_pair (hr : Computable r) (n x : ℕ) :
    eval (selfCode M hr) (Nat.pair n x) = acc M r (selfCode M hr) n x := by
  rw [eval_selfCode]
  simp [bigF]

theorem eval_patch_self (hr : Computable r) (m L y : ℕ) (h : L ≤ y) :
    eval (patchCode (selfCode M hr) m L) y = acc M r (selfCode M hr) m y := by
  rw [eval_patchCode]
  unfold patchFun
  rw [(by simp; omega : decide (y < L) = false)]
  simpa using eval_selfCode_pair M hr m y

theorem eval_patch_self_lt (hr : Computable r) (m L y : ℕ) (h : y < L) :
    eval (patchCode (selfCode M hr) m L) y = acc M r (selfCode M hr) 0 y := by
  rw [eval_patchCode]
  unfold patchFun
  rw [(by simp [h] : decide (y < L) = true)]
  simpa using eval_selfCode_pair M hr 0 y

/-- **Totality**: every level of the construction is defined everywhere. -/
theorem acc_dom_self (hr : Computable r) : ∀ x n, (acc M r (selfCode M hr) n x).Dom := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x IH =>
    have key : ∀ d n, x + 1 ≤ n + d → (acc M r (selfCode M hr) n x).Dom := by
      intro d
      induction d with
      | zero =>
        intro n hn
        refine acc_dom_of ?_
        intro i hi
        rw [contrib_of_lt (by omega)]
        trivial
      | succ d ihd =>
        intro n hn
        refine acc_dom_of ?_
        intro i hi
        by_cases hni : n ≤ i
        · have helig : ∀ y ≤ x, (elig M r (selfCode M hr) i y).Dom := by
            intro y hy
            refine elig_dom_of (maxK_dom _ _ ?_)
            intro L hL
            refine (M.dom_eq _ _).mpr ?_
            rw [eval_patch_self M hr (i+1) L y hL]
            rcases Nat.lt_or_ge y x with hyx | hyx
            · exact IH y hyx (i+1)
            · have hyx' : y = x := by omega
              subst hyx'
              exact ihd (i+1) (by omega)
          have hc : (cancelAt M r (selfCode M hr) i x).Dom :=
            cancelAt_dom_of (helig x le_rfl) (noElig_dom_of (fun y _ hy => helig y (by omega)))
          refine contrib_dom_of hc ?_
          intro hct
          exact (M.dom_eq _ _).mp (cost_dom_of_elig (cancelAt_mem_true_iff.mp hct).2.1)
        · rw [contrib_of_lt hni]; trivial
    intro n
    exact key (x+1) n (by omega)

theorem elig_dom_self (hr : Computable r) (i y : ℕ) :
    (elig M r (selfCode M hr) i y).Dom := by
  refine elig_dom_of (maxK_dom _ _ ?_)
  intro L hL
  refine (M.dom_eq _ _).mpr ?_
  rw [eval_patch_self M hr (i+1) L y hL]
  exact acc_dom_self M hr y (i+1)

theorem cancelAt_dom_self (hr : Computable r) (i x : ℕ) :
    (cancelAt M r (selfCode M hr) i x).Dom :=
  cancelAt_dom_of (elig_dom_self M hr i x)
    (noElig_dom_of (fun y _ _ => elig_dom_self M hr i y))

/-- The function computed by level `0` of the construction. -/
noncomputable def bigFun (hr : Computable r) (x : ℕ) : ℕ :=
  (acc M r (selfCode M hr) 0 x).get (acc_dom_self M hr x 0)

theorem bigFun_mem (hr : Computable r) (x : ℕ) :
    bigFun M hr x ∈ acc M r (selfCode M hr) 0 x := Part.get_mem _

theorem acc_zero_eq (hr : Computable r) (x : ℕ) :
    acc M r (selfCode M hr) 0 x = Part.some (bigFun M hr x) :=
  Part.eq_some_iff.mpr (bigFun_mem M hr x)

theorem bigFun_computable (hr : Computable r) : Computable (bigFun M hr) := by
  have h1 : Partrec fun x : ℕ => eval (selfCode M hr) (Nat.pair 0 x) :=
    eval_part.comp (Computable.const _)
      (Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.id)
  refine h1.of_eq (fun x => ?_)
  rw [eval_selfCode_pair, acc_zero_eq]
  rfl

theorem elig_false_of_not_true (hr : Computable r) (i y : ℕ)
    (h : ¬ (true ∈ elig M r (selfCode M hr) i y)) : false ∈ elig M r (selfCode M hr) i y := by
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp (elig_dom_self M hr i y)
  cases b with
  | true => exact absurd hb h
  | false => exact hb

theorem elig_true_of_not_false (hr : Computable r) (i y : ℕ)
    (h : ¬ (false ∈ elig M r (selfCode M hr) i y)) : true ∈ elig M r (selfCode M hr) i y := by
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp (elig_dom_self M hr i y)
  cases b with
  | true => exact hb
  | false => exact absurd hb h

theorem cancelAt_false_of_not_true (hr : Computable r) (i x : ℕ)
    (h : ¬ (true ∈ cancelAt M r (selfCode M hr) i x)) :
    false ∈ cancelAt M r (selfCode M hr) i x := by
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp (cancelAt_dom_self M hr i x)
  cases b with
  | true => exact absurd hb h
  | false => exact hb

/-- **Diagonalisation**: a program computing `bigFun` is never eligible at a stage beyond its
own index; equivalently, its cost always exceeds the bound. -/
theorem not_elig_of_computes (hr : Computable r) {i : ℕ}
    (hi : (ofNat Code i).eval = fun x => Part.some (bigFun M hr x)) :
    ∀ y, i ≤ y → false ∈ elig M r (selfCode M hr) i y := by
  classical
  intro y hiy
  by_contra hcon
  have htrue : true ∈ elig M r (selfCode M hr) i y := elig_true_of_not_false M hr i y hcon
  have hP : ∃ z, i ≤ z ∧ true ∈ elig M r (selfCode M hr) i z := ⟨y, hiy, htrue⟩
  obtain ⟨hiz, hz⟩ := Nat.find_spec hP
  have hno : true ∈ noElig M r (selfCode M hr) i (Nat.find hP) := by
    refine noElig_of ?_
    intro w hiw hwz
    refine elig_false_of_not_true M hr i w ?_
    intro hw
    exact absurd ⟨hiw, hw⟩ (Nat.find_min hP hwz)
  have hcanc : true ∈ cancelAt M r (selfCode M hr) i (Nat.find hP) :=
    cancelAt_mem_true_iff.mpr ⟨hiz, hz, hno⟩
  have hw : bigFun M hr (Nat.find hP) ∈ (ofNat Code i).eval (Nat.find hP) := by
    rw [hi]; exact Part.mem_some _
  have hc : bigFun M hr (Nat.find hP) + 1 ∈ contrib M r (selfCode M hr) 0 (Nat.find hP) i :=
    contrib_mem_of_cancel (Nat.zero_le i) hcanc hw
  have hle := acc_ge_contrib hiz (bigFun_mem M hr (Nat.find hP)) hc
  omega

/-- An index is cancelled at most at one stage. -/
theorem cancelAt_unique (hr : Computable r) {i x x' : ℕ}
    (h : true ∈ cancelAt M r (selfCode M hr) i x)
    (h' : true ∈ cancelAt M r (selfCode M hr) i x') : x = x' := by
  obtain ⟨hix, hex, hnx⟩ := cancelAt_mem_true_iff.mp h
  obtain ⟨hix', hex', hnx'⟩ := cancelAt_mem_true_iff.mp h'
  rcases Nat.lt_trichotomy x x' with hlt | heq | hgt
  · exact absurd (Part.mem_unique hex (noElig_spec hnx' x hix hlt)) (by simp)
  · exact heq
  · exact absurd (Part.mem_unique hex' (noElig_spec hnx x' hix' hgt)) (by simp)

/-- Each level agrees with level `0` from some point on. -/
theorem exists_patch_length (hr : Computable r) (n : ℕ) :
    ∃ L, ∀ x, L ≤ x → acc M r (selfCode M hr) n x = acc M r (selfCode M hr) 0 x := by
  classical
  induction n with
  | zero => exact ⟨0, fun x _ => rfl⟩
  | succ n ih =>
    obtain ⟨L, hL⟩ := ih
    have main : ∀ L' : ℕ, (∀ x, L' ≤ x → ¬ (true ∈ cancelAt M r (selfCode M hr) n x)) →
        ∀ x, max L L' ≤ x → acc M r (selfCode M hr) (n+1) x = acc M r (selfCode M hr) 0 x := by
      intro L' hL' x hx
      have h1 : acc M r (selfCode M hr) (n+1) x = acc M r (selfCode M hr) n x := by
        refine acc_congr ?_
        intro i hi
        by_cases hin : i = n
        · subst hin
          have hfalse : false ∈ cancelAt M r (selfCode M hr) i x :=
            cancelAt_false_of_not_true M hr i x (hL' x (by omega))
          rw [contrib_eq_of_not_cancel hfalse, contrib_eq_of_not_cancel hfalse]
        · exact contrib_eq_contrib_of_iff (by omega)
      rw [h1, hL x (by omega)]
    by_cases hex : ∃ x0, true ∈ cancelAt M r (selfCode M hr) n x0
    · obtain ⟨x0, hx0⟩ := hex
      refine ⟨max L (x0+1), fun x hx => main (x0+1) (fun z hz hcz => ?_) x (by omega)⟩
      have := cancelAt_unique M hr hcz hx0
      omega
    · push_neg at hex
      exact ⟨max L 0, fun x hx => main 0 (fun z _ hcz => hex z hcz) x (by omega)⟩

/-- A patched level computes exactly the function `bigFun`. -/
theorem eval_patchCode_eq (hr : Computable r) {n L : ℕ}
    (hL : ∀ x, L ≤ x → acc M r (selfCode M hr) n x = acc M r (selfCode M hr) 0 x) :
    eval (patchCode (selfCode M hr) n L) = fun y => Part.some (bigFun M hr y) := by
  funext y
  rcases Nat.lt_or_ge y L with h | h
  · rw [eval_patch_self_lt M hr n L y h, acc_zero_eq]
  · rw [eval_patch_self M hr n L y h, hL y h, acc_zero_eq]

end SelfRef

/-! ## A monotone majorant of the speedup factor -/

/-- The monotone majorant `rSup r m = max_{k ≤ m} r k`. -/
def rSup (r : ℕ → ℕ) (m : ℕ) : ℕ := Nat.rec (r 0) (fun k ih => max ih (r (k+1))) m

theorem le_rSup (r : ℕ → ℕ) (m : ℕ) : r m ≤ rSup r m := by
  cases m with
  | zero => exact le_rfl
  | succ k => exact le_max_right _ _

theorem rSup_mono (r : ℕ → ℕ) : Monotone (rSup r) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

theorem rSup_computable {r : ℕ → ℕ} (hr : Computable r) : Computable (rSup r) := by
  have h := Computable.nat_rec (f := fun m : ℕ => m) (g := fun _ : ℕ => r 0)
    (h := fun (_ : ℕ) (p : ℕ × ℕ) => max p.2 (r (p.1+1))) Computable.id (Computable.const (r 0))
    (Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (hr.comp (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))))
  exact h

/-! ## Blum's speedup theorem -/

/-- **Blum's speedup theorem.**  For *every* Blum complexity measure `M` and every computable
speedup factor `r` there is a computable function `f` such that every program `e` computing `f`
is beaten by another program `e'` for the same function: on almost every input, the cost of `e`
is at least `r` applied to the cost of `e'`.  Hence `f` has no fastest program. -/
theorem blum_speedup_of_measure (M : BlumMeasure) (r : ℕ → ℕ) (hr : Computable r) :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ e : Code, e.eval = (fun x => Part.some (f x)) →
        ∃ e' : Code, e'.eval = (fun x => Part.some (f x)) ∧
          ∀ᶠ x in Filter.atTop, ∃ a ∈ M.cost e' x, ∃ b ∈ M.cost e x, r a ≤ b := by
  have hR : Computable (rSup r) := rSup_computable hr
  refine ⟨bigFun M hR, bigFun_computable M hR, ?_⟩
  intro e he
  have hie : ofNat Code (encode e) = e := Denumerable.ofNat_encode e
  obtain ⟨L, hL⟩ := exists_patch_length M hR (encode e + 1)
  refine ⟨patchCode (selfCode M hR) (encode e + 1) L, eval_patchCode_eq M hR hL, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max (encode e) L)] with x hx
  have hdom_e' : (M.cost (patchCode (selfCode M hR) (encode e + 1) L) x).Dom := by
    refine (M.dom_eq _ _).mpr ?_
    rw [eval_patchCode_eq M hR hL]
    trivial
  obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hdom_e'
  have hdom_e : (M.cost e x).Dom := by
    refine (M.dom_eq _ _).mpr ?_
    rw [he]
    trivial
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hdom_e
  refine ⟨a, ha, b, hb, ?_⟩
  have hne : false ∈ elig M (rSup r) (selfCode M hR) (encode e) x :=
    not_elig_of_computes M hR (by rw [hie, he]) x (by omega)
  have hb' : b ∈ M.cost (ofNat Code (encode e)) x := by rw [hie]; exact hb
  obtain ⟨K, hK, hKb⟩ := cost_gt_of_not_elig hne hb'
  have haK : a ≤ K := maxK_ge (encode e + 1) x L (by omega) hK ha
  calc r a ≤ rSup r a := le_rSup r a
    _ ≤ rSup r K := rSup_mono r haK
    _ ≤ b := le_of_lt hKb

end CS

/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Strong

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

/-! ## A Blum measure exhibiting speedup -/

/-- The cost assigned to the `n`-th padding program at input `x`. -/
def costA (r : ℕ → ℕ) (n x : ℕ) : ℕ := r^[x - n] 0

/-- The cost floor imposed on every non-padding program at input `x`. -/
def bigB (r : ℕ → ℕ) (x : ℕ) : ℕ := r^[x + 1] 0

/-- Decides whether `e` is the `n`-th padding program for some `n ≤ x`. -/
def padLe (e : Code) (x : ℕ) : Bool := decide (padIdx e x ≤ x)

theorem padLe_iff (e : Code) (x : ℕ) : padLe e x = true ↔ padIdx e x ≤ x := by
  simp [padLe]

theorem padLe_primrec : Primrec fun p : Code × ℕ => padLe p.1 p.2 := by
  obtain ⟨_, h⟩ : PrimrecPred fun p : Code × ℕ => padIdx p.1 p.2 ≤ p.2 :=
    Primrec.nat_le.comp padIdx_primrec Primrec.snd
  exact h.of_eq (fun p => by simp [padLe])

theorem costA_computable {r : ℕ → ℕ} (hr : Computable r) :
    Computable fun q : ℕ × ℕ => costA r q.1 q.2 :=
  (iter_computable hr).comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst).to_comp

theorem bigB_computable {r : ℕ → ℕ} (hr : Computable r) : Computable fun x : ℕ => bigB r x :=
  (iter_computable hr).comp Primrec.succ.to_comp

theorem costA_step (r : ℕ → ℕ) (n x : ℕ) (h : n + 1 ≤ x) :
    r (costA r (n + 1) x) = costA r n x := by
  unfold costA
  have hx : x - n = (x - (n + 1)) + 1 := by omega
  rw [hx, Function.iterate_succ_apply']

theorem bigB_eq (r : ℕ → ℕ) (x : ℕ) : r (costA r 0 x) = bigB r x := by
  unfold costA bigB
  simp [Function.iterate_succ_apply']

attribute [local irreducible] stepGraph padIdx costA bigB padLe

section Speedup

variable (r : ℕ → ℕ)

/-- Graph of the measure `speedCost`. -/
def speedGraph (e : Code) (x m : ℕ) : Bool :=
  bif padLe e x then decide (m = costA r (padIdx e x) x)
  else (decide (bigB r x ≤ m) && stepGraph e x (m - bigB r x))

/-- A Blum complexity measure: the padding programs get the rapidly decreasing costs `costA`,
while every other program pays its step count plus the floor `bigB`. -/
noncomputable def speedCost (e : Code) (x : ℕ) : Part ℕ :=
  if padIdx e x ≤ x then Part.some (costA r (padIdx e x) x)
  else (stepCost e x).map (· + bigB r x)

theorem speedGraph_spec (e : Code) (x m : ℕ) :
    speedGraph r e x m = true ↔ m ∈ speedCost r e x := by
  unfold speedGraph speedCost
  by_cases h : padIdx e x ≤ x
  · rw [if_pos h]
    simp only [(padLe_iff e x).mpr h, cond_true, decide_eq_true_eq, Part.mem_some_iff]
  · rw [if_neg h]
    have hpl : padLe e x = false := by
      simpa using fun hc => h ((padLe_iff e x).mp hc)
    simp only [hpl, cond_false, Bool.and_eq_true, decide_eq_true_eq, Part.mem_map_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨m - bigB r x, (stepGraph_spec _ _ _).mp h2, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨by omega, ?_⟩
      have hsub : a + bigB r x - bigB r x = a := by omega
      rw [hsub]
      exact (stepGraph_spec _ _ _).mpr ha

theorem speedCost_dom (e : Code) (x : ℕ) : (speedCost r e x).Dom ↔ (e.eval x).Dom := by
  unfold speedCost
  by_cases h : padIdx e x ≤ x
  · rw [if_pos h, padIdx_le_imp h, eval_padCode]
    simp
  · rw [if_neg h]
    exact stepCost_dom e x

set_option maxHeartbeats 1000000 in
theorem speedGraph_computable (hr : Computable r) :
    Computable fun p : (Code × ℕ) × ℕ => speedGraph r p.1.1 p.1.2 p.2 := by
  have hpi : Computable fun p : (Code × ℕ) × ℕ => padIdx p.1.1 p.1.2 :=
    (padIdx_primrec.comp Primrec.fst).to_comp
  have hx : Computable fun p : (Code × ℕ) × ℕ => p.1.2 := (Primrec.snd.comp Primrec.fst).to_comp
  have hm : Computable fun p : (Code × ℕ) × ℕ => p.2 := Computable.snd
  have hA : Computable fun p : (Code × ℕ) × ℕ => costA r (padIdx p.1.1 p.1.2) p.1.2 :=
    (costA_computable hr).comp (hpi.pair hx)
  have hBig : Computable fun p : (Code × ℕ) × ℕ => bigB r p.1.2 := (bigB_computable hr).comp hx
  have hcond : Computable fun p : (Code × ℕ) × ℕ => padLe p.1.1 p.1.2 :=
    (padLe_primrec.comp Primrec.fst).to_comp
  have hleft : Computable fun p : (Code × ℕ) × ℕ =>
      decide (p.2 = costA r (padIdx p.1.1 p.1.2) p.1.2) :=
    computable_decide_eq.comp (hm.pair hA)
  have hstepArg : Computable fun p : (Code × ℕ) × ℕ => ((p.1.1, p.1.2), p.2 - bigB r p.1.2) :=
    Computable.fst.pair (Primrec.nat_sub.to_comp.comp hm hBig)
  have hstep : Computable fun p : (Code × ℕ) × ℕ =>
      stepGraph p.1.1 p.1.2 (p.2 - bigB r p.1.2) :=
    stepGraph_computable.comp hstepArg
  have hright : Computable fun p : (Code × ℕ) × ℕ =>
      (decide (bigB r p.1.2 ≤ p.2) && stepGraph p.1.1 p.1.2 (p.2 - bigB r p.1.2)) :=
    Primrec.and.to_comp.comp (computable_decide_le.comp (hBig.pair hm)) hstep
  exact Computable.cond hcond hleft hright

/-- The Blum complexity measure witnessing speedup. -/
noncomputable def speedMeasure (hr : Computable r) : BlumMeasure where
  cost := speedCost r
  graph := speedGraph r
  graph_computable := speedGraph_computable r hr
  graph_spec := speedGraph_spec r
  dom_eq := speedCost_dom r

theorem speedCost_pad (n x : ℕ) (h : n ≤ x) :
    speedCost r (padCode n) x = Part.some (costA r n x) := by
  unfold speedCost
  rw [padIdx_pad n x h, if_pos h]

theorem speedCost_not_pad {e : Code} (he : ∀ n, e ≠ padCode n) (x : ℕ) :
    speedCost r e x = (stepCost e x).map (· + bigB r x) := by
  unfold speedCost
  rw [if_neg (padIdx_not_pad e he x)]

end Speedup

/-! ## Blum's speedup phenomenon: a problem with no fastest algorithm -/

/-- **A Blum complexity measure exhibiting speedup.**

For every computable "speedup factor" `r` there is a Blum complexity measure `M` (i.e. a
measure satisfying Blum's axioms for the standard numbering of the partial computable
functions) and a computable function `f` such that *every* program `e` computing `f` is beaten
by another program `e'` computing the very same function `f`: on almost every input `x`, the
cost of `e` is at least `r` applied to the cost of `e'`.

Thus no program for `f` is optimal: each one can be sped up by a factor `r` on almost all
inputs. -/
theorem blum_speedup_padding_measure (r : ℕ → ℕ) (hr : Computable r) :
    ∃ (M : BlumMeasure) (f : ℕ → ℕ), Computable f ∧
      ∀ e : Code, e.eval = (fun x => Part.some (f x)) →
        ∃ e' : Code, e'.eval = (fun x => Part.some (f x)) ∧
          ∀ᶠ x in Filter.atTop, ∃ a ∈ M.cost e' x, ∃ b ∈ M.cost e x, r a ≤ b := by
  refine ⟨speedMeasure r hr, fun _ => 0, Computable.const 0, ?_⟩
  intro e he
  by_cases hpad : ∃ n, e = padCode n
  · obtain ⟨n, rfl⟩ := hpad
    refine ⟨padCode (n + 1), funext fun x => eval_padCode _ _, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (n + 1)] with x hx
    refine ⟨costA r (n + 1) x, ?_, costA r n x, ?_, ?_⟩
    · show costA r (n + 1) x ∈ speedCost r (padCode (n + 1)) x
      rw [speedCost_pad r (n + 1) x hx]
      simp
    · show costA r n x ∈ speedCost r (padCode n) x
      rw [speedCost_pad r n x (by omega)]
      simp
    · rw [costA_step r n x hx]
  · push_neg at hpad
    refine ⟨padCode 0, funext fun x => eval_padCode _ _, ?_⟩
    filter_upwards with x
    have hdom : (stepCost e x).Dom := by
      refine (stepCost_dom e x).mpr ?_
      rw [he]
      trivial
    obtain ⟨s, hs⟩ := Part.dom_iff_mem.mp hdom
    refine ⟨costA r 0 x, ?_, s + bigB r x, ?_, ?_⟩
    · show costA r 0 x ∈ speedCost r (padCode 0) x
      rw [speedCost_pad r 0 x (Nat.zero_le x)]
      simp
    · show s + bigB r x ∈ speedCost r e x
      rw [speedCost_not_pad r hpad x]
      exact Part.mem_map_iff _ |>.mpr ⟨s, hs, rfl⟩
    · rw [bigB_eq r x]
      omega

/-- **There are problems with no fastest algorithm** (Blum's speedup theorem).

Fix any Blum complexity measure `M` (a cost function for the standard numbering of the partial
computable functions satisfying Blum's axioms) and any computable "speedup factor" `r`.  Then
there is a computable function `f` such that *every* program `e` computing `f` is beaten by
another program `e'` computing the very same function: on almost every input `x`, the cost of
`e` is at least `r` applied to the cost of `e'`.

Thus no program for `f` is optimal: each one can be sped up by the factor `r` on almost all
inputs. -/
theorem blum_speedup (M : BlumMeasure) (r : ℕ → ℕ) (hr : Computable r) :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ e : Code, e.eval = (fun x => Part.some (f x)) →
        ∃ e' : Code, e'.eval = (fun x => Part.some (f x)) ∧
          ∀ᶠ x in Filter.atTop, ∃ a ∈ M.cost e' x, ∃ b ∈ M.cost e x, r a ≤ b :=
  blum_speedup_of_measure M r hr

/-- Blum's speedup theorem for the concrete step-counting measure: there is a computable
function whose every program is sped up by the factor `r`, almost everywhere, by another
program for the same function. -/
theorem blum_speedup_stepMeasure (r : ℕ → ℕ) (hr : Computable r) :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ e : Code, e.eval = (fun x => Part.some (f x)) →
        ∃ e' : Code, e'.eval = (fun x => Part.some (f x)) ∧
          ∀ᶠ x in Filter.atTop,
            ∃ a ∈ stepMeasure.cost e' x, ∃ b ∈ stepMeasure.cost e x, r a ≤ b :=
  blum_speedup_of_measure stepMeasure r hr

end CS

