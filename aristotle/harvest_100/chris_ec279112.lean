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

import RequestProject.Blum.Cost

/-!
# The Blum speedup construction

We build, by the recursion theorem, a code `blumCode` computing a two-parameter family of
functions `f i t` (`i` an index bound, `t` a patch threshold) with the following features.

At stage `x`, the function `f i 0` diagonalises against every program `j ≥ i` which is
*cheap at stage `x`*, meaning that `cost j x ≤ M j x + x` where `M j x` is the maximal cost of
the programs `curry blumCode ⟨j+1, t⟩` (`t ≤ x`) on input `x`.  Each program is diagonalised
against at the first stage at which it becomes cheap, so `f i 0` and `f 0 0` differ at only
finitely many arguments; the parameter `t` lets one patch those finitely many arguments,
so that `f (j+1) t = f 0 0` for a suitable `t`.
-/

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code Primrec

/-! ### Generic form of the construction, parameterised by a cost function -/

/-- Maximal cost, according to `cf`, of the auxiliary programs with parameters `(j+1, t)`,
`t ≤ y`, on input `y`. -/
def Mg (cf : ℕ → ℕ) (j y : ℕ) : ℕ :=
  (List.range (y + 1)).foldr (fun t s => max (cf (Nat.pair (Nat.pair (j + 1) t) y)) s) 0

/-- Program `j` is *cheap at stage `y`*: it converges on `y` within `Mg cf j y + y` steps. -/
def critg (cf : ℕ → ℕ) (j y : ℕ) : Bool :=
  (evaln (Mg cf j y + y) (Denumerable.ofNat Code j) y).isSome

/-- The value that program `j` returns on input `y` (when it is cheap at stage `y`). -/
def dvalg (cf : ℕ → ℕ) (j y : ℕ) : ℕ :=
  (evaln (Mg cf j y + y) (Denumerable.ofNat Code j) y).getD 0

/-- Program `j` is cancelled at stage `x`: `x` is the first stage `> j` at which `j` is cheap. -/
def fcg (cf : ℕ → ℕ) (j x : ℕ) : Bool :=
  decide (j < x) && critg cf j x &&
    (List.range x).foldr (fun y b => (decide (y ≤ j) || !critg cf j y) && b) true

/-- The diagonal value at stage `x` of the `i`-th function of the family. -/
def Fg (cf : ℕ → ℕ) (i x : ℕ) : ℕ :=
  1 + (List.range x).foldr
      (fun j s => if decide (i ≤ j) && fcg cf j x then max (dvalg cf j x) s else s) 0

/-! ### The fuel-bounded (computable) version -/

/-- The least `k' ≤ k` such that `evaln k' e a` converges (and `0` if there is none). -/
def costF (e : Code) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if (evaln k e a).isSome then costF e a k
    else if (evaln (k + 1) e a).isSome then k + 1 else 0

/-- `Mg` computed with fuel `k`. -/
def MF (e : Code) (k j y : ℕ) : ℕ := Mg (fun a => costF e a k) j y

/-- `critg` computed with fuel `k`. -/
def critF (e : Code) (k j y : ℕ) : Bool := critg (fun a => costF e a k) j y

/-- `dvalg` computed with fuel `k`. -/
def dvalF (e : Code) (k j y : ℕ) : ℕ := dvalg (fun a => costF e a k) j y

/-- `fcg` computed with fuel `k`. -/
def fcF (e : Code) (k j x : ℕ) : Bool := fcg (fun a => costF e a k) j x

/-- `Fg` computed with fuel `k`. -/
def FF (e : Code) (k i x : ℕ) : ℕ := Fg (fun a => costF e a k) i x

/-- Fuel `k` suffices for all the recursive calls needed to compute the value at `(i, t, x)`. -/
def okF (e : Code) (k i t x : ℕ) : Bool :=
  if x < t then (evaln k e (Nat.pair (Nat.pair 0 0) x)).isSome
  else (List.range (Nat.pair (Nat.pair x x) x + 1)).foldr (fun a b =>
        ((!(decide (i + 1 ≤ a.unpair.1.unpair.1) && decide (a.unpair.1.unpair.1 ≤ x) &&
              decide (a.unpair.2 ≤ x) && decide (a.unpair.1.unpair.2 ≤ a.unpair.2)))
          || (evaln k e a).isSome) && b) true

/-- One fuel-bounded attempt at computing the value of the construction on input `a`. -/
def bigOpt (e : Code) (k a : ℕ) : Option ℕ :=
  if okF e k a.unpair.1.unpair.1 a.unpair.1.unpair.2 a.unpair.2 then
    some (if a.unpair.2 < a.unpair.1.unpair.2 then
            (evaln k e (Nat.pair (Nat.pair 0 0) a.unpair.2)).getD 0
          else FF e k a.unpair.1.unpair.1 a.unpair.2)
  else none

/-! ### Computability -/

theorem costF_eq_rec (e : Code) (a k : ℕ) :
    costF e a k = Nat.rec 0 (fun n IH => if (evaln n e a).isSome then IH
      else if (evaln (n + 1) e a).isSome then n + 1 else 0) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [costF, ih]

theorem primrec_costF : Primrec₂ fun (p : Code × ℕ) (k : ℕ) => costF p.1 p.2 k := by
  have hev : Primrec fun q : (Code × ℕ) × ℕ × ℕ => (evaln q.2.1 q.1.1 q.1.2).isSome :=
    option_isSome.comp (primrec_evaln.comp
      (((fst.comp snd).pair (fst.comp fst)).pair (snd.comp fst)))
  have hev2 : Primrec fun q : (Code × ℕ) × ℕ × ℕ => (evaln (q.2.1 + 1) q.1.1 q.1.2).isSome :=
    option_isSome.comp (primrec_evaln.comp
      (((Primrec.succ.comp (fst.comp snd)).pair (fst.comp fst)).pair (snd.comp fst)))
  have hg : Primrec₂ fun (p : Code × ℕ) (q : ℕ × ℕ) =>
      if (evaln q.1 p.1 p.2).isSome then q.2
      else if (evaln (q.1 + 1) p.1 p.2).isSome then q.1 + 1 else 0 :=
    Primrec.ite (Primrec.primrecPred (by simpa using hev)) (snd.comp snd)
      (Primrec.ite (Primrec.primrecPred (by simpa using hev2))
        (Primrec.succ.comp (fst.comp snd)) (const 0))
  exact (Primrec.nat_rec (f := fun _ : Code × ℕ => (0 : ℕ)) (const 0) hg).of_eq
    (fun p k => (costF_eq_rec p.1 p.2 k).symm)

theorem primrec_MF : Primrec fun p : (Code × ℕ) × ℕ × ℕ => MF p.1.1 p.1.2 p.2.1 p.2.2 := by
  have hrange : Primrec fun p : (Code × ℕ) × ℕ × ℕ => List.range (p.2.2 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (snd.comp snd))
  have hstep : Primrec₂ fun (p : (Code × ℕ) × ℕ × ℕ) (q : ℕ × ℕ) =>
      max (costF p.1.1 (Nat.pair (Nat.pair (p.2.1 + 1) q.1) p.2.2) p.1.2) q.2 := by
    have hcost : Primrec fun r : ((Code × ℕ) × ℕ × ℕ) × ℕ × ℕ =>
        costF r.1.1.1 (Nat.pair (Nat.pair (r.1.2.1 + 1) r.2.1) r.1.2.2) r.1.1.2 :=
      primrec_costF.comp
        ((fst.comp (fst.comp fst)).pair
          (Primrec₂.natPair.comp
            (Primrec₂.natPair.comp (Primrec.succ.comp (fst.comp (snd.comp fst)))
              (fst.comp snd))
            (snd.comp (snd.comp fst))))
        (snd.comp (fst.comp fst))
    exact Primrec.nat_max.comp hcost (snd.comp snd)
  exact Primrec.list_foldr hrange (const 0) hstep

theorem primrec_evalnF : Primrec fun p : (Code × ℕ) × ℕ × ℕ =>
    evaln (MF p.1.1 p.1.2 p.2.1 p.2.2 + p.2.2) (Denumerable.ofNat Code p.2.1) p.2.2 :=
  primrec_evaln.comp
    (((Primrec.nat_add.comp primrec_MF (snd.comp snd)).pair
      ((Primrec.ofNat Code).comp (fst.comp snd))).pair (snd.comp snd))

theorem primrec_critF : Primrec fun p : (Code × ℕ) × ℕ × ℕ => critF p.1.1 p.1.2 p.2.1 p.2.2 :=
  option_isSome.comp primrec_evalnF

theorem primrec_dvalF : Primrec fun p : (Code × ℕ) × ℕ × ℕ => dvalF p.1.1 p.1.2 p.2.1 p.2.2 :=
  Primrec.option_getD.comp primrec_evalnF (const 0)

theorem primrec_fcF : Primrec fun p : (Code × ℕ) × ℕ × ℕ => fcF p.1.1 p.1.2 p.2.1 p.2.2 := by
  have hall : Primrec fun p : (Code × ℕ) × ℕ × ℕ =>
      (List.range p.2.2).foldr
        (fun y b => (decide (y ≤ p.2.1) || !critF p.1.1 p.1.2 p.2.1 y) && b) true := by
    have hstep : Primrec₂ fun (p : (Code × ℕ) × ℕ × ℕ) (q : ℕ × Bool) =>
        (decide (q.1 ≤ p.2.1) || !critF p.1.1 p.1.2 p.2.1 q.1) && q.2 := by
      have hc : Primrec fun r : ((Code × ℕ) × ℕ × ℕ) × ℕ × Bool =>
          critF r.1.1.1 r.1.1.2 r.1.2.1 r.2.1 :=
        primrec_critF.comp ((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair (fst.comp snd)))
      exact Primrec.and.comp
        (Primrec.or.comp
          (PrimrecPred.decide (PrimrecRel.comp nat_le (fst.comp snd) (fst.comp (snd.comp fst))))
          (Primrec.not.comp hc)) (snd.comp snd)
    exact Primrec.list_foldr (Primrec.list_range.comp (snd.comp snd)) (const true) hstep
  exact Primrec.and.comp (Primrec.and.comp
    (PrimrecPred.decide (PrimrecRel.comp nat_lt (fst.comp snd) (snd.comp snd))) primrec_critF) hall

theorem primrec_FF : Primrec fun p : (Code × ℕ) × ℕ × ℕ => FF p.1.1 p.1.2 p.2.1 p.2.2 := by
  have hstep : Primrec₂ fun (p : (Code × ℕ) × ℕ × ℕ) (q : ℕ × ℕ) =>
      if decide (p.2.1 ≤ q.1) && fcF p.1.1 p.1.2 q.1 p.2.2 then
        max (dvalF p.1.1 p.1.2 q.1 p.2.2) q.2
      else q.2 := by
    have harg : Primrec fun r : ((Code × ℕ) × ℕ × ℕ) × ℕ × ℕ =>
        ((r.1.1.1, r.1.1.2), (r.2.1, r.1.2.2)) :=
      ((fst.comp (fst.comp fst)).pair (snd.comp (fst.comp fst))).pair
        ((fst.comp snd).pair (snd.comp (snd.comp fst)))
    have hfc : Primrec fun r : ((Code × ℕ) × ℕ × ℕ) × ℕ × ℕ => fcF r.1.1.1 r.1.1.2 r.2.1 r.1.2.2 :=
      primrec_fcF.comp harg
    have hdv : Primrec fun r : ((Code × ℕ) × ℕ × ℕ) × ℕ × ℕ =>
        dvalF r.1.1.1 r.1.1.2 r.2.1 r.1.2.2 := primrec_dvalF.comp harg
    have hcond : Primrec fun r : ((Code × ℕ) × ℕ × ℕ) × ℕ × ℕ =>
        decide (r.1.2.1 ≤ r.2.1) && fcF r.1.1.1 r.1.1.2 r.2.1 r.1.2.2 :=
      Primrec.and.comp
        (PrimrecPred.decide (PrimrecRel.comp nat_le (fst.comp (snd.comp fst)) (fst.comp snd))) hfc
    exact Primrec.ite (Primrec.primrecPred (by simpa using hcond))
      (Primrec.nat_max.comp hdv (snd.comp snd)) (snd.comp snd)
  exact Primrec.nat_add.comp (const 1)
    (Primrec.list_foldr (Primrec.list_range.comp (snd.comp snd)) (const 0) hstep)

theorem primrec_okF :
    Primrec fun p : (Code × ℕ) × ℕ × ℕ × ℕ => okF p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2 := by
  have hstep : Primrec₂ fun (p : (Code × ℕ) × ℕ × ℕ × ℕ) (q : ℕ × Bool) =>
      ((!(decide (p.2.1 + 1 ≤ q.1.unpair.1.unpair.1) && decide (q.1.unpair.1.unpair.1 ≤ p.2.2.2) &&
            decide (q.1.unpair.2 ≤ p.2.2.2) && decide (q.1.unpair.1.unpair.2 ≤ q.1.unpair.2)))
        || (evaln p.1.2 p.1.1 q.1).isSome) && q.2 := by
    have hq : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.2.1 := fst.comp snd
    have hu1 : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.2.1.unpair.1.unpair.1 :=
      fst.comp (Primrec.unpair.comp (fst.comp (Primrec.unpair.comp hq)))
    have hu2 : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.2.1.unpair.1.unpair.2 :=
      snd.comp (Primrec.unpair.comp (fst.comp (Primrec.unpair.comp hq)))
    have hu3 : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.2.1.unpair.2 :=
      snd.comp (Primrec.unpair.comp hq)
    have hx : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.1.2.2.2 :=
      snd.comp (snd.comp (snd.comp fst))
    have hi : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.1.2.1 :=
      fst.comp (snd.comp fst)
    have hev : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool =>
        (evaln r.1.1.2 r.1.1.1 r.2.1).isSome :=
      option_isSome.comp (primrec_evaln.comp
        (((snd.comp (fst.comp fst)).pair (fst.comp (fst.comp fst))).pair hq))
    exact Primrec.and.comp
      (Primrec.or.comp (Primrec.not.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
        (PrimrecPred.decide (PrimrecRel.comp nat_le (Primrec.succ.comp hi) hu1))
        (PrimrecPred.decide (PrimrecRel.comp nat_le hu1 hx)))
        (PrimrecPred.decide (PrimrecRel.comp nat_le hu3 hx)))
        (PrimrecPred.decide (PrimrecRel.comp nat_le hu2 hu3)))) hev) (snd.comp snd)
  have hx : Primrec fun p : (Code × ℕ) × ℕ × ℕ × ℕ => p.2.2.2 := snd.comp (snd.comp snd)
  have hbranch2 := Primrec.list_foldr
      (f := fun p : (Code × ℕ) × ℕ × ℕ × ℕ =>
        List.range (Nat.pair (Nat.pair p.2.2.2 p.2.2.2) p.2.2.2 + 1))
      (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec₂.natPair.comp (Primrec₂.natPair.comp hx hx) hx))) (const true) hstep
  have hbranch1 : Primrec fun p : (Code × ℕ) × ℕ × ℕ × ℕ =>
      (evaln p.1.2 p.1.1 (Nat.pair (Nat.pair 0 0) p.2.2.2)).isSome :=
    option_isSome.comp (primrec_evaln.comp
      (((snd.comp fst).pair (fst.comp fst)).pair
        (Primrec₂.natPair.comp (Primrec₂.natPair.comp (const 0) (const 0)) hx)))
  exact Primrec.ite
    (PrimrecRel.comp nat_lt (snd.comp (snd.comp snd)) (fst.comp (snd.comp snd)))
    hbranch1 hbranch2

theorem primrec_bigOpt : Primrec fun p : (Code × ℕ) × ℕ => bigOpt p.1.1 p.2 p.1.2 := by
  have hi : Primrec fun p : (Code × ℕ) × ℕ => p.1.2.unpair.1.unpair.1 :=
    fst.comp (Primrec.unpair.comp (fst.comp (Primrec.unpair.comp (snd.comp fst))))
  have ht : Primrec fun p : (Code × ℕ) × ℕ => p.1.2.unpair.1.unpair.2 :=
    snd.comp (Primrec.unpair.comp (fst.comp (Primrec.unpair.comp (snd.comp fst))))
  have hx : Primrec fun p : (Code × ℕ) × ℕ => p.1.2.unpair.2 :=
    snd.comp (Primrec.unpair.comp (snd.comp fst))
  have hok : Primrec fun p : (Code × ℕ) × ℕ =>
      okF p.1.1 p.2 p.1.2.unpair.1.unpair.1 p.1.2.unpair.1.unpair.2 p.1.2.unpair.2 :=
    primrec_okF.comp (((fst.comp fst).pair snd).pair (hi.pair (ht.pair hx)))
  have hv1 : Primrec fun p : (Code × ℕ) × ℕ =>
      (evaln p.2 p.1.1 (Nat.pair (Nat.pair 0 0) p.1.2.unpair.2)).getD 0 :=
    Primrec.option_getD.comp
      (primrec_evaln.comp
        ((snd.pair (fst.comp fst)).pair
          (Primrec₂.natPair.comp (Primrec₂.natPair.comp (const 0) (const 0)) hx))) (const 0)
  have hv2 : Primrec fun p : (Code × ℕ) × ℕ =>
      FF p.1.1 p.2 p.1.2.unpair.1.unpair.1 p.1.2.unpair.2 :=
    primrec_FF.comp (((fst.comp fst).pair snd).pair (hi.pair hx))
  exact Primrec.ite (Primrec.primrecPred (by simpa using hok))
    (Primrec.option_some.comp
      (Primrec.ite (PrimrecRel.comp nat_lt hx ht) hv1 hv2)) (const none)

theorem partrec_bigStep :
    Partrec₂ fun (e : Code) (a : ℕ) => Nat.rfindOpt (fun k => bigOpt e k a) :=
  Partrec.rfindOpt (f := fun (p : Code × ℕ) (k : ℕ) => bigOpt p.1 k p.2)
    (Primrec.to_comp primrec_bigOpt)

/-- The code produced by the recursion theorem: it computes the whole Blum family,
including the self-referential cost comparisons. -/
noncomputable def blumCode : Code := Classical.choose (fixed_point₂ partrec_bigStep)

theorem blumCode_eval (a : ℕ) :
    eval blumCode a = Nat.rfindOpt (fun k => bigOpt blumCode k a) :=
  congrFun (Classical.choose_spec (fixed_point₂ partrec_bigStep)) a

end CS

import Mathlib

/-!
# A Blum complexity measure on Mathlib's partial recursive codes

We use Mathlib's step-indexed interpreter `Nat.Partrec.Code.evaln` to define a
complexity measure `CS.cost c n`: the least amount of fuel with which the code `c`
returns a value on input `n`.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The Blum complexity measure: `cost c n` is the least fuel `k` such that
`evaln k c n` returns a value (and `0` if the computation never converges). -/
noncomputable def cost (c : Code) (n : ℕ) : ℕ := sInf {k | (evaln k c n).isSome}

theorem cost_le {c : Code} {n k : ℕ} (h : (evaln k c n).isSome) : cost c n ≤ k :=
  Nat.sInf_le h

theorem halts_iff {c : Code} {n : ℕ} : (eval c n).Dom ↔ ∃ k, (evaln k c n).isSome := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := evaln_complete.1 (Part.get_mem h)
    exact ⟨k, by rw [Option.mem_def] at hk; simp [hk]⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
    exact Part.dom_iff_mem.2 ⟨x, evaln_sound (by simpa using hx)⟩

theorem isSome_evaln_cost {c : Code} {n : ℕ} (h : (eval c n).Dom) :
    (evaln (cost c n) c n).isSome :=
  Nat.sInf_mem (halts_iff.1 h)

theorem isSome_evaln_of_cost_le {c : Code} {n k : ℕ} (h : (eval c n).Dom) (hk : cost c n ≤ k) :
    (evaln k c n).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (isSome_evaln_cost h)
  have : x ∈ evaln k c n := evaln_mono hk (by simpa using hx)
  rw [Option.mem_def] at this
  simp [this]

theorem cost_le_iff {c : Code} {n k : ℕ} (h : (eval c n).Dom) :
    cost c n ≤ k ↔ (evaln k c n).isSome :=
  ⟨fun hk => isSome_evaln_of_cost_le h hk, fun hk => cost_le hk⟩

theorem lt_cost_of_not_isSome {c : Code} {n k : ℕ} (h : (eval c n).Dom)
    (hk : ¬ (evaln k c n).isSome) : k < cost c n := by
  by_contra hc
  exact hk (isSome_evaln_of_cost_le h (by omega))

/-- The value computed with any sufficient amount of fuel is the value of the program. -/
theorem evaln_getD_eq {c : Code} {n k v : ℕ} (h : eval c n = Part.some v)
    (hk : (evaln k c n).isSome) : (evaln k c n).getD 0 = v := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
  have hmem : x ∈ eval c n := evaln_sound (by simpa using hx)
  rw [h] at hmem
  simp [hx, Part.mem_some_iff.1 hmem]

/-! ### Fuel bounds for `const`, `id` and `curry` -/

theorem evaln_const (m x k : ℕ) (hx : x < k) (hm : m < k) :
    evaln k (Code.const m) x = some m := by
  induction m with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [Code.const, evaln, Nat.lt_succ_iff.1 hx]
  | succ m ih =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hm' : m < k' + 1 := by omega
    simp [Code.const, evaln, Nat.lt_succ_iff.1 hx, ih hm', Nat.lt_succ_iff.1 hm']

theorem evaln_id {x k : ℕ} (hx : x < k) : evaln k Code.id x = some x := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [Code.id, evaln, Nat.lt_succ_iff.1 hx, Seq.seq]

theorem evaln_curry {e : Code} {a x k : ℕ} (hk : Nat.pair a x < k) :
    evaln k (curry e a) x = evaln k e (Nat.pair a x) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hx : x < k' + 1 := lt_of_le_of_lt (Nat.right_le_pair a x) hk
  have ha : a < k' + 1 := lt_of_le_of_lt (Nat.left_le_pair a x) hk
  simp [curry, evaln, Nat.lt_succ_iff.1 hx, evaln_const a x _ hx ha, evaln_id hx, Seq.seq]

theorem cost_curry_le {e : Code} {a x : ℕ} (h : (eval e (Nat.pair a x)).Dom) :
    cost (curry e a) x ≤ cost e (Nat.pair a x) := by
  have hs : (evaln (cost e (Nat.pair a x)) e (Nat.pair a x)).isSome := isSome_evaln_cost h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  have hb : Nat.pair a x < cost e (Nat.pair a x) := evaln_bound (by simpa using hv)
  exact cost_le (by rw [evaln_curry hb]; simp [hv])

end CS

