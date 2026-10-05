import Mathlib
import RequestProject.Hardness

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Cook–Levin theorem

`SAT` is NP-complete:

* `SAT ∈ NP`, and
* every language in `NP` reduces to `SAT`.

Here languages are sets of bit strings; a language is in `NP` when it is decided by a
family of polynomial size Boolean circuits reading the input word together with a
witness word of polynomial length (`Frontier.InNP`).  `SAT` is the set of bit strings
whose associated CNF formula is satisfiable (`Frontier.SATlang`), the association being
the occurrence-matrix encoding of `Frontier.decodeCNF`.

The reductions produced here are *projections*: each output bit is a constant, or a bit
of the input word, or the negation of a bit of the input word, and the number of output
bits is polynomial in the length of the input word (`Frontier.IsProjectionReduction`).
In particular they are computable by polynomial size circuits.

The circuit families witnessing membership in `NP` are not required to be uniformly
generated, so `Frontier.InNP` is the non-uniform version of `NP`; correspondingly the
reductions produced by the hardness proof are non-uniform (but they are projections,
which is a much more restrictive class than polynomial time computable maps).
-/

namespace Frontier

/-- `L₁` reduces to `L₂` by a projection reduction. -/
def ReducesTo (L₁ L₂ : Set (List Bool)) : Prop :=
  ∃ f : List Bool → List Bool, IsProjectionReduction f ∧ ∀ x, x ∈ L₁ ↔ f x ∈ L₂

/-- `L` is NP-hard: every language of NP reduces to it. -/
def NPHard (L : Set (List Bool)) : Prop := ∀ L' : Set (List Bool), InNP L' → ReducesTo L' L

/-- `L` is NP-complete. -/
def NPComplete (L : Set (List Bool)) : Prop := InNP L ∧ NPHard L

/-- **The Cook–Levin theorem**: SAT is NP-complete. -/
theorem cook_levin : NPComplete SATlang := by
  refine ⟨SATlang_inNP, ?_⟩
  rintro L ⟨V⟩
  exact ⟨red V, red_isProjection V, red_mem_SAT V⟩

/-! ### Sanity checks: SAT is a nontrivial language -/

/-- The bit string `[false, false]` denotes the formula consisting of one empty clause,
which is unsatisfiable. -/
theorem not_mem_SATlang_example : ([false, false] : List Bool) ∉ SATlang := by
  rintro ⟨a, ha⟩
  simp [decodeCNF, decodeClause, bitIdx, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval] at ha

/-- The bit string `[true, false]` denotes the formula `x₀`, which is satisfiable. -/
theorem mem_SATlang_example : ([true, false] : List Bool) ∈ SATlang := by
  refine ⟨fun _ => true, ?_⟩
  simp [decodeCNF, decodeClause, bitIdx, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval]

end Frontier

import Mathlib
import RequestProject.Encoding
import RequestProject.Poly

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The class NP, the language SAT, and `SAT ∈ NP`

A language is a set of bit strings.  It is in `NP` when membership can be checked by a
polynomial size circuit reading the input word together with a polynomially long
witness word.
-/

namespace Frontier

open Std.Sat

/-- The circuit input assignment given by an input word `x` and a witness word `w`:
variables `0, …, |x|-1` carry the input, variables `|x|, |x|+1, …` the witness. -/
def assign (x w : List Bool) : ℕ → Bool :=
  fun i => if i < x.length then x.getD i false else w.getD (i - x.length) false

/-- A nondeterministic polynomial time verifier for the language `L`, given by a
polynomial size family of circuits. -/
structure NPVerifier (L : Set (List Bool)) where
  /-- length of the witness for inputs of length `n` -/
  wlen : ℕ → ℕ
  /-- the verifying circuit for inputs of length `n` -/
  circ : ℕ → Circ
  wf : ∀ n, Circ.WF (circ n)
  wlen_poly : Poly wlen
  size_poly : Poly (fun n => (circ n).length)
  spec : ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length = wlen x.length ∧
      Circ.eval (circ x.length) (assign x w) = true

/-- The class NP. -/
def InNP (L : Set (List Bool)) : Prop := Nonempty (NPVerifier L)

/-- The language SAT: bit strings denoting a satisfiable CNF formula. -/
def SATlang : Set (List Bool) := {s | ∃ a : ℕ → Bool, CNF.eval a (decodeCNF s) = true}

/-! ### SAT is in NP -/

/-- The formula checking that literal `j` satisfies clause `i`, for an input of length `l`. -/
def satLitTree (l k i j : ℕ) : Tree :=
  .disj (.conj (.var (bitIdx k i j true)) (.var (l + j)))
    (.conj (.var (bitIdx k i j false)) (.neg (.var (l + j))))

/-- The verifying formula for SAT on inputs of length `l`. -/
def satTree (l : ℕ) : Tree :=
  Tree.bigAnd ((List.range (Nat.sqrt (l / 2))).map (fun i =>
    Tree.bigOr ((List.range (Nat.sqrt (l / 2))).map (fun j =>
      satLitTree l (Nat.sqrt (l / 2)) i j))))

theorem anyCongrMem {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.any_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem allCongrMem {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.all_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem two_sqrt_sq_le (l : ℕ) : 2 * Nat.sqrt (l / 2) * Nat.sqrt (l / 2) ≤ l := by
  have h1 : Nat.sqrt (l / 2) * Nat.sqrt (l / 2) ≤ l / 2 := Nat.sqrt_le (l / 2)
  calc 2 * Nat.sqrt (l / 2) * Nat.sqrt (l / 2)
      = 2 * (Nat.sqrt (l / 2) * Nat.sqrt (l / 2)) := by ring
    _ ≤ 2 * (l / 2) := by omega
    _ ≤ l := by omega

theorem satLitTree_size (l k i j : ℕ) : (satLitTree l k i j).size = 8 := by
  simp [satLitTree, Tree.size]

theorem satTree_size (l : ℕ) :
    (satTree l).size ≤ (9 * Nat.sqrt (l / 2) + 2) * Nat.sqrt (l / 2) + 1 := by
  set k := Nat.sqrt (l / 2)
  refine le_trans (Tree.bigAnd_size _ (9 * k + 1) ?_) ?_
  · intro t ht
    simp only [List.mem_map, List.mem_range] at ht
    obtain ⟨i, _, rfl⟩ := ht
    refine le_trans (Tree.bigOr_size _ 8 ?_) ?_
    · intro u hu
      simp only [List.mem_map, List.mem_range] at hu
      obtain ⟨j, _, rfl⟩ := hu
      exact le_of_eq (satLitTree_size l k i j)
    · simp only [List.length_map, List.length_range]
      omega
  · simp only [List.length_map, List.length_range]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right k (by omega)) 1

/-- Evaluation of the verifying formula. -/
theorem satTree_eval (l : ℕ) (X : ℕ → Bool) :
    (satTree l).eval X =
      (List.range (Nat.sqrt (l / 2))).all (fun i =>
        (List.range (Nat.sqrt (l / 2))).any (fun j => (satLitTree l (Nat.sqrt (l / 2)) i j).eval X)) := by
  simp [satTree, List.all_map, List.any_map, Function.comp_def]

/-- The value of a decoded clause, written as a big disjunction. -/
theorem clause_eval_decodeClause (s : List Bool) (k i : ℕ) (a : ℕ → Bool) :
    CNF.Clause.eval a (decodeClause s k i) =
      (List.range k).any (fun j =>
        (s.getD (bitIdx k i j true) false && a j) ||
        (s.getD (bitIdx k i j false) false && !(a j))) := by
  simp only [CNF.Clause.eval, decodeClause, List.any_filter, List.any_flatMap]
  refine anyCongrMem ?_
  intro j _
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  cases a j <;> simp

theorem eval_congr_lt {f : CNF ℕ} {k : ℕ} (hf : ∀ c ∈ f, ∀ l ∈ c, l.1 < k) {a a' : ℕ → Bool}
    (h : ∀ i, i < k → a i = a' i) : CNF.eval a f = CNF.eval a' f := by
  simp only [CNF.eval]
  refine allCongrMem ?_
  intro c hc
  simp only [CNF.Clause.eval]
  refine anyCongrMem ?_
  intro l hl
  rw [h l.1 (hf c hc l hl)]

theorem assign_bit (s w : List Bool) {k i j : ℕ} (b : Bool) (hk : k = Nat.sqrt (s.length / 2))
    (hi : i < k) (hj : j < k) :
    assign s w (bitIdx k i j b) = s.getD (bitIdx k i j b) false := by
  have h1 : bitIdx k i j b < 2 * k * k := bitIdx_lt b hi hj
  have h2 : 2 * k * k ≤ s.length := by rw [hk]; exact two_sqrt_sq_le _
  simp only [assign]
  rw [if_pos (by omega)]

theorem assign_wit (s w : List Bool) (j : ℕ) : assign s w (s.length + j) = w.getD j false := by
  simp only [assign]
  rw [if_neg (by omega)]
  congr 1
  omega

theorem satLitTree_eval (s w : List Bool) {k i j : ℕ} (hk : k = Nat.sqrt (s.length / 2))
    (hi : i < k) (hj : j < k) :
    (satLitTree s.length k i j).eval (assign s w)
      = (s.getD (bitIdx k i j true) false && w.getD j false ||
          s.getD (bitIdx k i j false) false && !(w.getD j false)) := by
  simp [satLitTree, Tree.eval, assign_bit s w true hk hi hj, assign_bit s w false hk hi hj,
    assign_wit s w j]

/-- The verifying circuit for SAT accepts `(s, w)` exactly when the assignment described
by `w` satisfies the formula denoted by `s`. -/
theorem satTree_correct (s w : List Bool) :
    Circ.eval ((satTree s.length).compile 0) (assign s w) = true ↔
      CNF.eval (fun j => w.getD j false) (decodeCNF s) = true := by
  rw [Tree.compile_eval, satTree_eval, decodeCNF, CNF.eval, List.all_map]
  simp only [Function.comp_def, List.all_eq_true, List.mem_range]
  constructor
  · intro h i hi
    rw [clause_eval_decodeClause,
      ← anyCongrMem (fun j hj => satLitTree_eval s w rfl hi (by simpa using hj))]
    exact h i hi
  · intro h i hi
    rw [anyCongrMem (fun j hj => satLitTree_eval s w rfl hi (by simpa using hj))]
    have h2 := h i hi
    rwa [clause_eval_decodeClause] at h2

theorem decodeCNF_vars (s : List Bool) :
    ∀ c ∈ decodeCNF s, ∀ lit ∈ c, lit.1 < Nat.sqrt (s.length / 2) := by
  intro c hc lit hlit
  rw [decodeCNF, List.mem_map] at hc
  obtain ⟨i, _, rfl⟩ := hc
  have : (lit.1, lit.2) ∈ decodeClause s (Nat.sqrt (s.length / 2)) i := by simpa using hlit
  exact (mem_decodeClause.mp this).1

/-- SAT is in NP. -/
theorem SATlang_inNP : InNP SATlang := by
  refine ⟨{
    wlen := fun l => Nat.sqrt (l / 2)
    circ := fun l => (satTree l).compile 0
    wf := fun l => Tree.compile_wf' _
    wlen_poly := Poly.mono Poly.id (fun n => le_trans (Nat.sqrt_le_self _) (Nat.div_le_self _ _))
    size_poly := ?_
    spec := ?_ }⟩
  · refine Poly.mono (f := fun l => ((satTree l).compile 0).length)
      (g := fun l => (9 * l + 2) * l + 1) ?_ ?_
    · exact ((Poly.mul (Poly.add (Poly.mul (Poly.const 9) Poly.id) (Poly.const 2)) Poly.id).add
        (Poly.const 1))
    · intro l
      show ((satTree l).compile 0).length ≤ (9 * l + 2) * l + 1
      rw [Tree.compile_length]
      refine le_trans (satTree_size l) ?_
      have hk : Nat.sqrt (l / 2) ≤ l := le_trans (Nat.sqrt_le_self _) (Nat.div_le_self _ _)
      exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) hk) 1
  · intro s
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨(List.range (Nat.sqrt (s.length / 2))).map a, by simp, ?_⟩
      rw [satTree_correct]
      rw [eval_congr_lt (decodeCNF_vars s)
        (a := fun j => ((List.range (Nat.sqrt (s.length / 2))).map a).getD j false) (a' := a) ?_]
      · exact ha
      · intro i hi
        show ((List.range (Nat.sqrt (s.length / 2))).map a).getD i false = a i
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simpa using hi)]
        simp
    · rintro ⟨w, _, hw⟩
      exact ⟨fun j => w.getD j false, (satTree_correct s w).mp hw⟩

end Frontier

import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Boolean circuits

A circuit is a straight-line program: a list of gates, where gate number `j` may refer
to the values of gates with smaller index (this is the well-formedness condition `Circ.WF`).
Gates may also read input variables, indexed by `ℕ`.

The value of the circuit is the value of its last gate.

We also introduce *formulas* (`Tree`) together with a compiler into straight-line programs;
this is only a convenience for *constructing* circuits.
-/

namespace Frontier

/-- A single gate of a straight-line program. -/
inductive Gate where
  | inp (i : ℕ)
  | const (b : Bool)
  | neg (j : ℕ)
  | conj (j k : ℕ)
  | disj (j k : ℕ)
  deriving DecidableEq, Repr

namespace Gate

/-- Value of a gate, given the input assignment `x` and the list of values of the
previous gates. -/
def eval (x : ℕ → Bool) (vs : List Bool) : Gate → Bool
  | .inp i => x i
  | .const b => b
  | .neg j => !(vs.getD j false)
  | .conj j k => (vs.getD j false) && (vs.getD k false)
  | .disj j k => (vs.getD j false) || (vs.getD k false)

/-- A gate sitting at position `j` is well formed if it only refers to earlier gates. -/
def WFAt (j : ℕ) : Gate → Prop
  | .inp _ => True
  | .const _ => True
  | .neg k => k < j
  | .conj k l => k < j ∧ l < j
  | .disj k l => k < j ∧ l < j

end Gate

/-- A circuit: a straight-line program. -/
abbrev Circ := List Gate

/-- Values of all gates, starting from an already computed prefix `vs`. -/
def valsAux (x : ℕ → Bool) (vs : List Bool) (gs : Circ) : List Bool :=
  gs.foldl (fun vs g => vs ++ [Gate.eval x vs g]) vs

/-- The list of values of all gates of the circuit. -/
def vals (x : ℕ → Bool) (gs : Circ) : List Bool := valsAux x [] gs

theorem valsAux_nil (x : ℕ → Bool) (vs : List Bool) : valsAux x vs [] = vs := rfl

theorem valsAux_append (x : ℕ → Bool) (vs : List Bool) (gs hs : Circ) :
    valsAux x vs (gs ++ hs) = valsAux x (valsAux x vs gs) hs := by
  simp [valsAux, List.foldl_append]

theorem valsAux_concat (x : ℕ → Bool) (vs : List Bool) (gs : Circ) (g : Gate) :
    valsAux x vs (gs ++ [g]) = valsAux x vs gs ++ [Gate.eval x (valsAux x vs gs) g] := by
  simp [valsAux]

theorem valsAux_prefix (x : ℕ → Bool) (gs : Circ) :
    ∀ vs : List Bool, ∃ ws, valsAux x vs gs = vs ++ ws ∧ ws.length = gs.length := by
  induction gs with
  | nil => intro vs; exact ⟨[], by simp [valsAux]⟩
  | cons g gs ih =>
      intro vs
      obtain ⟨ws, hws, hlen⟩ := ih (vs ++ [Gate.eval x vs g])
      refine ⟨Gate.eval x vs g :: ws, ?_, by simp [hlen]⟩
      have : valsAux x vs (g :: gs) = valsAux x (vs ++ [Gate.eval x vs g]) gs := rfl
      rw [this, hws]; simp

theorem valsAux_length (x : ℕ → Bool) (gs : Circ) (vs : List Bool) :
    (valsAux x vs gs).length = vs.length + gs.length := by
  obtain ⟨ws, hws, hlen⟩ := valsAux_prefix x gs vs
  simp [hws, hlen]

@[simp] theorem vals_length (x : ℕ → Bool) (gs : Circ) : (vals x gs).length = gs.length := by
  simp [vals, valsAux_length]

theorem vals_append (x : ℕ → Bool) (gs hs : Circ) :
    ∃ ws, vals x (gs ++ hs) = vals x gs ++ ws ∧ ws.length = hs.length := by
  rw [vals, valsAux_append]
  exact valsAux_prefix x hs (vals x gs)

/-- Values of gates in a prefix of the circuit do not change when the circuit is extended. -/
theorem vals_getD_append (x : ℕ → Bool) (gs hs : Circ) {j : ℕ} (hj : j < gs.length) :
    (vals x (gs ++ hs)).getD j false = (vals x gs).getD j false := by
  obtain ⟨ws, hws, _⟩ := vals_append x gs hs
  rw [hws]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa using hj)]

theorem vals_concat (x : ℕ → Bool) (gs : Circ) (g : Gate) :
    vals x (gs ++ [g]) = vals x gs ++ [Gate.eval x (vals x gs) g] := by
  simp [vals, valsAux_concat]

theorem vals_getD_concat (x : ℕ → Bool) (gs : Circ) (g : Gate) :
    (vals x (gs ++ [g])).getD gs.length false = Gate.eval x (vals x gs) g := by
  rw [vals_concat]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- The value at position `j` is obtained by applying the gate at position `j` to the
full list of values (legitimate because the gate only refers to earlier positions). -/
theorem vals_getD_eq (x : ℕ → Bool) {gs : Circ} {j : ℕ} {g : Gate}
    (hwf : ∀ k g', gs[k]? = some g' → Gate.WFAt k g') (hj : gs[j]? = some g) :
    (vals x gs).getD j false = Gate.eval x (vals x gs) g := by
  have hjlt : j < gs.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    exact absurd hj (by simp)
  obtain ⟨pre, suf, hpre, hsplit⟩ : ∃ pre suf : Circ, pre.length = j ∧ gs = (pre ++ [g]) ++ suf := by
    refine ⟨gs.take j, gs.drop (j + 1), by simp; omega, ?_⟩
    have hget : gs[j] = g := by
      have h := List.getElem?_eq_getElem hjlt
      rw [h] at hj
      exact Option.some.inj hj
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hjlt, hget]
    simp
  have hstable : ∀ k, k < j → (vals x gs).getD k false = (vals x pre).getD k false := by
    intro k hk
    conv_lhs => rw [hsplit]
    rw [vals_getD_append x (pre ++ [g]) suf (by simp; omega),
      vals_getD_append x pre [g] (by omega)]
  have h1 : (vals x gs).getD j false = Gate.eval x (vals x pre) g := by
    conv_lhs => rw [hsplit]
    rw [vals_getD_append x (pre ++ [g]) suf (by simp; omega), ← hpre, vals_getD_concat]
  rw [h1]
  cases g with
  | inp i => simp [Gate.eval]
  | const b => simp [Gate.eval]
  | neg k =>
      have hk : k < j := hwf j _ hj
      simp only [Gate.eval, hstable k hk]
  | conj k l =>
      obtain ⟨hk, hl⟩ : k < j ∧ l < j := hwf j _ hj
      simp only [Gate.eval, hstable k hk, hstable l hl]
  | disj k l =>
      obtain ⟨hk, hl⟩ : k < j ∧ l < j := hwf j _ hj
      simp only [Gate.eval, hstable k hk, hstable l hl]

/-- Well-formedness of a circuit: every gate only refers to earlier gates. -/
def Circ.WF (gs : Circ) : Prop := ∀ (j : ℕ) (g : Gate), gs[j]? = some g → Gate.WFAt j g

theorem Circ.wf_concat {gs : Circ} {g : Gate} (hgs : Circ.WF gs)
    (hg : Gate.WFAt gs.length g) : Circ.WF (gs ++ [g]) := by
  intro j g' hj
  rcases lt_or_ge j gs.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hj
    exact hgs j g' hj
  · rw [List.getElem?_append_right hge] at hj
    have : j - gs.length = 0 := by
      by_contra hne
      rw [List.getElem?_eq_none (by simp; omega)] at hj
      exact absurd hj (by simp)
    have hjeq : j = gs.length := by omega
    subst hjeq
    simp at hj
    subst hj
    exact hg

/-- The value computed by a circuit. -/
def Circ.eval (gs : Circ) (x : ℕ → Bool) : Bool := (vals x gs).getD (gs.length - 1) false

/-! ### Formulas and their compilation to circuits -/

/-- Propositional formulas over variables indexed by `ℕ`. -/
inductive Tree where
  | var (i : ℕ)
  | lit (b : Bool)
  | neg (t : Tree)
  | conj (t u : Tree)
  | disj (t u : Tree)
  deriving Repr

namespace Tree

/-- Value of a formula. -/
def eval (x : ℕ → Bool) : Tree → Bool
  | .var i => x i
  | .lit b => b
  | .neg t => !(t.eval x)
  | .conj t u => (t.eval x) && (u.eval x)
  | .disj t u => (t.eval x) || (u.eval x)

/-- Number of nodes of a formula. -/
def size : Tree → ℕ
  | .var _ => 1
  | .lit _ => 1
  | .neg t => t.size + 1
  | .conj t u => t.size + u.size + 1
  | .disj t u => t.size + u.size + 1

theorem size_pos (t : Tree) : 0 < t.size := by
  cases t <;> simp [size]

/-- Compile a formula into a straight-line program that is meant to be placed at
position `base` of a larger circuit. -/
def compile (base : ℕ) : Tree → Circ
  | .var i => [Gate.inp i]
  | .lit b => [Gate.const b]
  | .neg t => t.compile base ++ [Gate.neg (base + t.size - 1)]
  | .conj t u =>
      t.compile base ++ u.compile (base + t.size) ++
        [Gate.conj (base + t.size - 1) (base + t.size + u.size - 1)]
  | .disj t u =>
      t.compile base ++ u.compile (base + t.size) ++
        [Gate.disj (base + t.size - 1) (base + t.size + u.size - 1)]

@[simp] theorem compile_length (t : Tree) (base : ℕ) : (t.compile base).length = t.size := by
  induction t generalizing base with
  | var i => simp [compile, size]
  | lit b => simp [compile, size]
  | neg t ih => simp [compile, size, ih]
  | conj t u iht ihu => simp [compile, size, iht, ihu]; omega
  | disj t u iht ihu => simp [compile, size, iht, ihu]; omega

theorem compile_spec (x : ℕ → Bool) (t : Tree) (base : ℕ) (pre : Circ) (h : pre.length = base) :
    (vals x (pre ++ t.compile base)).getD (base + t.size - 1) false = t.eval x := by
  induction t generalizing base pre with
  | var i =>
      have : base + size (Tree.var i) - 1 = pre.length := by simp [size, h]
      rw [this]
      simpa [compile, Gate.eval, eval] using vals_getD_concat x pre (Gate.inp i)
  | lit b =>
      have : base + size (Tree.lit b) - 1 = pre.length := by simp [size, h]
      rw [this]
      simpa [compile, Gate.eval, eval] using vals_getD_concat x pre (Gate.const b)
  | neg t ih =>
      have happ : pre ++ (Tree.neg t).compile base
          = (pre ++ t.compile base) ++ [Gate.neg (base + t.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen : (pre ++ t.compile base).length = base + t.size := by simp [h]
      have hidx : base + (Tree.neg t).size - 1 = (pre ++ t.compile base).length := by
        have := t.size_pos; simp [size, hlen]
      rw [happ, hidx, vals_getD_concat]
      simp only [Gate.eval, eval]
      rw [ih base pre h]
  | conj t u iht ihu =>
      have happ : pre ++ (Tree.conj t u).compile base
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)) ++
              [Gate.conj (base + t.size - 1) (base + t.size + u.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen1 : (pre ++ t.compile base).length = base + t.size := by simp [h]
      have hlen2 : ((pre ++ t.compile base) ++ u.compile (base + t.size)).length
          = base + t.size + u.size := by simp [h]; omega
      have hidx : base + (Tree.conj t u).size - 1
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)).length := by
        have h1 := t.size_pos
        have h2 := u.size_pos
        rw [hlen2]
        simp only [size]
        omega
      rw [happ, hidx, vals_getD_concat]
      simp only [Gate.eval, eval]
      have h1 : (vals x ((pre ++ t.compile base) ++ u.compile (base + t.size))).getD
          (base + t.size - 1) false = t.eval x := by
        rw [vals_getD_append x _ _ (by rw [hlen1]; have := t.size_pos; omega)]
        exact iht base pre h
      have h2 : (vals x ((pre ++ t.compile base) ++ u.compile (base + t.size))).getD
          (base + t.size + u.size - 1) false = u.eval x := by
        have := ihu (base + t.size) (pre ++ t.compile base) hlen1
        rw [show base + t.size + u.size - 1 = base + t.size + u.size - 1 from rfl]
        simpa using this
      rw [h1, h2]
  | disj t u iht ihu =>
      have happ : pre ++ (Tree.disj t u).compile base
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)) ++
              [Gate.disj (base + t.size - 1) (base + t.size + u.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen1 : (pre ++ t.compile base).length = base + t.size := by simp [h]
      have hlen2 : ((pre ++ t.compile base) ++ u.compile (base + t.size)).length
          = base + t.size + u.size := by simp [h]; omega
      have hidx : base + (Tree.disj t u).size - 1
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)).length := by
        have h1 := t.size_pos
        have h2 := u.size_pos
        rw [hlen2]
        simp only [size]
        omega
      rw [happ, hidx, vals_getD_concat]
      simp only [Gate.eval, eval]
      have h1 : (vals x ((pre ++ t.compile base) ++ u.compile (base + t.size))).getD
          (base + t.size - 1) false = t.eval x := by
        rw [vals_getD_append x _ _ (by rw [hlen1]; have := t.size_pos; omega)]
        exact iht base pre h
      have h2 : (vals x ((pre ++ t.compile base) ++ u.compile (base + t.size))).getD
          (base + t.size + u.size - 1) false = u.eval x := by
        have := ihu (base + t.size) (pre ++ t.compile base) hlen1
        simpa using this
      rw [h1, h2]

/-- The compiled circuit of a formula computes the value of the formula. -/
theorem compile_eval (x : ℕ → Bool) (t : Tree) : Circ.eval (t.compile 0) x = t.eval x := by
  have := compile_spec x t 0 [] (by simp)
  simpa [Circ.eval] using this

theorem compile_wf (t : Tree) (base : ℕ) (pre : Circ) (h : pre.length = base)
    (hpre : Circ.WF pre) : Circ.WF (pre ++ t.compile base) := by
  induction t generalizing base pre with
  | var i =>
      exact Circ.wf_concat hpre (by simp [Gate.WFAt])
  | lit b =>
      exact Circ.wf_concat hpre (by simp [Gate.WFAt])
  | neg t ih =>
      have happ : pre ++ (Tree.neg t).compile base
          = (pre ++ t.compile base) ++ [Gate.neg (base + t.size - 1)] := by
        simp [compile, List.append_assoc]
      rw [happ]
      refine Circ.wf_concat (ih base pre h hpre) ?_
      have := t.size_pos
      simp only [Gate.WFAt, List.length_append, compile_length, h]
      omega
  | conj t u iht ihu =>
      have happ : pre ++ (Tree.conj t u).compile base
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)) ++
              [Gate.conj (base + t.size - 1) (base + t.size + u.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen1 : (pre ++ t.compile base).length = base + t.size := by simp [h]
      rw [happ]
      refine Circ.wf_concat (ihu (base + t.size) _ hlen1 (iht base pre h hpre)) ?_
      have h1 := t.size_pos
      have h2 := u.size_pos
      simp only [Gate.WFAt, List.length_append, compile_length, h]
      omega
  | disj t u iht ihu =>
      have happ : pre ++ (Tree.disj t u).compile base
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)) ++
              [Gate.disj (base + t.size - 1) (base + t.size + u.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen1 : (pre ++ t.compile base).length = base + t.size := by simp [h]
      rw [happ]
      refine Circ.wf_concat (ihu (base + t.size) _ hlen1 (iht base pre h hpre)) ?_
      have h1 := t.size_pos
      have h2 := u.size_pos
      simp only [Gate.WFAt, List.length_append, compile_length, h]
      omega

theorem compile_wf' (t : Tree) : Circ.WF (t.compile 0) := by
  have := compile_wf t 0 [] (by simp) (fun j g hg => by simp at hg)
  simpa using this

/-- Conjunction of a list of formulas. -/
def bigAnd : List Tree → Tree
  | [] => .lit true
  | t :: ts => .conj t (bigAnd ts)

/-- Disjunction of a list of formulas. -/
def bigOr : List Tree → Tree
  | [] => .lit false
  | t :: ts => .disj t (bigOr ts)

@[simp] theorem bigAnd_eval (x : ℕ → Bool) (l : List Tree) :
    (bigAnd l).eval x = l.all (fun t => t.eval x) := by
  induction l with
  | nil => simp [bigAnd, eval]
  | cons t ts ih => simp [bigAnd, eval, ih]

@[simp] theorem bigOr_eval (x : ℕ → Bool) (l : List Tree) :
    (bigOr l).eval x = l.any (fun t => t.eval x) := by
  induction l with
  | nil => simp [bigOr, eval]
  | cons t ts ih => simp [bigOr, eval, ih]

theorem bigAnd_size (l : List Tree) (B : ℕ) (h : ∀ t ∈ l, t.size ≤ B) :
    (bigAnd l).size ≤ (B + 1) * l.length + 1 := by
  induction l with
  | nil => simp [bigAnd, size]
  | cons t ts ih =>
      have h1 : t.size ≤ B := h t (by simp)
      have h2 := ih (fun u hu => h u (by simp [hu]))
      simp only [bigAnd, size, List.length_cons]
      have : (B + 1) * (ts.length + 1) + 1 = (B + 1) * ts.length + 1 + B + 1 := by ring
      omega

theorem bigOr_size (l : List Tree) (B : ℕ) (h : ∀ t ∈ l, t.size ≤ B) :
    (bigOr l).size ≤ (B + 1) * l.length + 1 := by
  induction l with
  | nil => simp [bigOr, size]
  | cons t ts ih =>
      have h1 : t.size ≤ B := h t (by simp)
      have h2 := ih (fun u hu => h u (by simp [hu]))
      simp only [bigOr, size, List.length_cons]
      have : (B + 1) * (ts.length + 1) + 1 = (B + 1) * ts.length + 1 + B + 1 := by ring
      omega

end Tree

end Frontier

import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Polynomial bounds

A tiny library about functions `ℕ → ℕ` that are bounded by a polynomial.
-/

namespace Frontier

/-- `Poly g` says that `g` is bounded by a polynomial. -/
def Poly (g : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, g n ≤ c * (n + 1) ^ d

theorem Poly.mono {f g : ℕ → ℕ} (hg : Poly g) (h : ∀ n, f n ≤ g n) : Poly f := by
  obtain ⟨c, d, hc⟩ := hg
  exact ⟨c, d, fun n => le_trans (h n) (hc n)⟩

theorem Poly.const (c : ℕ) : Poly (fun _ => c) := by
  refine ⟨c, 0, fun n => ?_⟩
  simp

theorem Poly.id : Poly (fun n => n) := by
  refine ⟨1, 1, fun n => ?_⟩
  simp

theorem Poly.add {f g : ℕ → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun n => f n + g n) := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 + c2, max d1 d2, fun n => ?_⟩
  have hp1 : (n + 1) ^ d1 ≤ (n + 1) ^ (max d1 d2) :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (le_max_left _ _)
  have hp2 : (n + 1) ^ d2 ≤ (n + 1) ^ (max d1 d2) :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (le_max_right _ _)
  calc f n + g n ≤ c1 * (n + 1) ^ d1 + c2 * (n + 1) ^ d2 := Nat.add_le_add (h1 n) (h2 n)
    _ ≤ c1 * (n + 1) ^ (max d1 d2) + c2 * (n + 1) ^ (max d1 d2) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hp1) (Nat.mul_le_mul_left _ hp2)
    _ = (c1 + c2) * (n + 1) ^ (max d1 d2) := by ring

theorem Poly.mul {f g : ℕ → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun n => f n * g n) := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 * c2, d1 + d2, fun n => ?_⟩
  calc f n * g n ≤ (c1 * (n + 1) ^ d1) * (c2 * (n + 1) ^ d2) := Nat.mul_le_mul (h1 n) (h2 n)
    _ = c1 * c2 * (n + 1) ^ (d1 + d2) := by ring

end Frontier

import Mathlib
import RequestProject.NP

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## NP-hardness of SAT

Given a verifier for `L`, the reduction maps an input word `x` of length `n` to the
bit string encoding the Tseitin CNF of the verifying circuit `C n`, in which the input
variables are fixed to the bits of `x` and the witness variables are left free.

Every bit of the produced string is a constant or a bit of `x` or its negation, i.e.
the reduction is a *projection*.
-/

namespace Frontier

open Std.Sat

/-- A bit string transformation which is computed bit-by-bit from single bits of the
input word, with polynomially many output bits. -/
def IsProjectionReduction (f : List Bool → List Bool) : Prop :=
  ∃ P : ℕ → List ProjBit,
    (∀ x : List Bool, f x = (P x.length).map (fun p => p.eval x)) ∧ Poly (fun n => (P n).length)

/-! ### Auxiliary facts about instantiation -/

theorem inst_append (x : List Bool) (F G : PCnf) :
    PCnf.inst x (F ++ G) = PCnf.inst x F ++ PCnf.inst x G := by
  simp [PCnf.inst]

@[simp] theorem inst_length (x : List Bool) (F : PCnf) : (PCnf.inst x F).length = F.length := by
  simp [PCnf.inst]

theorem inst_vars {x : List Bool} {F : PCnf} {B : ℕ} (h : ∀ c ∈ F, ∀ l ∈ c, l.1 < B) :
    ∀ c ∈ PCnf.inst x F, ∀ l ∈ c, l.1 < B := by
  intro c hc l hl
  rw [PCnf.inst, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  rw [PClause.inst, List.mem_map] at hl
  obtain ⟨p, hp, rfl⟩ := hl
  exact h c' hc' p hp

/-! ### Structural facts about the parametric Tseitin CNF -/

theorem mem_tseitinP {mode : ℕ → Option ProjBit} {gs : Circ} {c : PClause}
    (hc : c ∈ tseitinP mode gs) : ∃ j g, gs[j]? = some g ∧ c ∈ gateClausesP mode j g := by
  rw [tseitinP, List.mem_flatMap] at hc
  obtain ⟨⟨g, j⟩, hmem, hc⟩ := hc
  exact ⟨j, g, List.mem_zipIdx_iff_getElem?.mp hmem, hc⟩

theorem getElem?_lt {gs : Circ} {j : ℕ} {g : Gate} (hg : gs[j]? = some g) : j < gs.length := by
  by_contra h
  rw [List.getElem?_eq_none (by omega)] at hg
  exact absurd hg (by simp)

theorem gateClausesP_length (mode : ℕ → Option ProjBit) (j : ℕ) (g : Gate) :
    (gateClausesP mode j g).length ≤ 3 := by
  cases g with
  | inp i => cases hm : mode i <;> simp [gateClausesP, hm]
  | const b => simp [gateClausesP]
  | neg k => simp [gateClausesP]
  | conj k l => simp [gateClausesP]
  | disj k l => simp [gateClausesP]

theorem tseitinP_length (mode : ℕ → Option ProjBit) (gs : Circ) :
    (tseitinP mode gs).length ≤ 3 * gs.length := by
  rw [tseitinP, List.length_flatMap]
  have h : ∀ y ∈ (gs.zipIdx.map (fun p => (gateClausesP mode p.2 p.1).length)), y ≤ 3 := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨p, _, rfl⟩ := hy
    exact gateClausesP_length mode p.2 p.1
  refine le_trans (List.sum_le_card_nsmul _ 3 h) ?_
  simp [mul_comm]

theorem tseitinP_vars {mode : ℕ → Option ProjBit} {gs : Circ} {M : ℕ} (hwf : Circ.WF gs)
    (hM : ∀ i, mode i = none → i < M) :
    ∀ c ∈ tseitinP mode gs, ∀ l ∈ c, l.1 < 2 * gs.length + 2 * M + 1 := by
  intro c hc l hl
  obtain ⟨j, g, hg, hc⟩ := mem_tseitinP hc
  have hjlt : j < gs.length := getElem?_lt hg
  cases g with
  | inp i =>
      cases hm : mode i with
      | some p =>
          simp only [gateClausesP, hm, List.mem_singleton] at hc
          subst hc
          simp only [List.mem_singleton] at hl
          subst hl
          simp only [gv]
          omega
      | none =>
          have hi : i < M := hM i hm
          simp only [gateClausesP, hm, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
            rcases hl with rfl | rfl <;> simp only [gv, iv] <;> omega
  | const b =>
      simp only [gateClausesP, List.mem_singleton] at hc
      subst hc
      simp only [List.mem_singleton] at hl
      subst hl
      simp only [gv]
      omega
  | neg k =>
      have hk : k < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl <;> simp only [gv] <;> omega
  | conj k l' =>
      obtain ⟨hk, hl'⟩ : k < j ∧ l' < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl | rfl <;> simp only [gv] <;> omega
  | disj k l' =>
      obtain ⟨hk, hl'⟩ : k < j ∧ l' < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl | rfl <;> simp only [gv] <;> omega

theorem tseitinP_consistent {mode : ℕ → Option ProjBit} {gs : Circ} (hwf : Circ.WF gs) :
    ∀ c ∈ tseitinP mode gs, PClause.Consistent c := by
  intro c hc
  obtain ⟨j, g, hg, hc⟩ := mem_tseitinP hc
  cases g with
  | inp i =>
      cases hm : mode i with
      | some p =>
          simp only [gateClausesP, hm, List.mem_singleton] at hc
          subst hc
          intro p1 h1 q1 h2 _
          simp only [List.mem_singleton] at h1 h2
          subst h1; subst h2; rfl
      | none =>
          simp only [gateClausesP, hm, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;>
            · intro p1 h1 q1 h2 hpq
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
              rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
                simp_all [gv, iv] <;> omega
  | const b =>
      simp only [gateClausesP, List.mem_singleton] at hc
      subst hc
      intro p1 h1 q1 h2 _
      simp only [List.mem_singleton] at h1 h2
      subst h1; subst h2; rfl
  | neg k =>
      have hk : k < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        · intro p1 h1 q1 h2 hpq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp_all [gv]
  | conj k l' =>
      obtain ⟨hk, hl'⟩ : k < j ∧ l' < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · intro p1 h1 q1 h2 hpq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
          rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;> simp_all [gv]
  | disj k l' =>
      obtain ⟨hk, hl'⟩ : k < j ∧ l' < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · intro p1 h1 q1 h2 hpq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
          rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;> simp_all [gv]

/-! ### The reduction -/

variable {L : Set (List Bool)}

/-- Which input variables of the verifying circuit are fixed, and to what. -/
def redMode (V : NPVerifier L) (n : ℕ) : ℕ → Option ProjBit :=
  fun i => if i < n then some (.pos i) else if i < n + V.wlen n then none else some (.cst false)

/-- The parametric CNF produced by the reduction on inputs of length `n`. -/
def redP (V : NPVerifier L) (n : ℕ) : PCnf :=
  tseitinP (redMode V n) (V.circ n) ++
    (if (V.circ n).length = 0 then [([] : PClause)]
      else [[(gv ((V.circ n).length - 1), ProjBit.cst true)]])

/-- The number of variables/clauses of the encoding produced by the reduction. -/
def redK (V : NPVerifier L) (n : ℕ) : ℕ := 5 * (V.circ n).length + 2 * (n + V.wlen n) + 2

/-- The projection bits of the reduction on inputs of length `n`. -/
def redBits (V : NPVerifier L) (n : ℕ) : List ProjBit := encodeCNFP (redK V n) (redP V n)

/-- The reduction. -/
def red (V : NPVerifier L) (x : List Bool) : List Bool :=
  (redBits V x.length).map (fun p => p.eval x)

theorem redP_consistent (V : NPVerifier L) (n : ℕ) :
    ∀ c ∈ redP V n, PClause.Consistent c := by
  intro c hc
  rw [redP, List.mem_append] at hc
  rcases hc with hc | hc
  · exact tseitinP_consistent (V.wf n) c hc
  · split at hc
    · simp only [List.mem_singleton] at hc
      subst hc
      intro p1 h1 q1 h2 _
      simp at h1
    · simp only [List.mem_singleton] at hc
      subst hc
      intro p1 h1 q1 h2 _
      simp only [List.mem_singleton] at h1 h2
      subst h1; subst h2; rfl

theorem redP_length (V : NPVerifier L) (n : ℕ) : (redP V n).length ≤ redK V n := by
  rw [redP, List.length_append, redK]
  have h1 := tseitinP_length (redMode V n) (V.circ n)
  have h2 : (if (V.circ n).length = 0 then [([] : PClause)]
      else [[(gv ((V.circ n).length - 1), ProjBit.cst true)]]).length = 1 := by
    split <;> simp
  omega

theorem redMode_none (V : NPVerifier L) (n : ℕ) :
    ∀ i, redMode V n i = none → i < n + V.wlen n := by
  intro i hi
  simp only [redMode] at hi
  split at hi
  · exact absurd hi (by simp)
  · split at hi
    · assumption
    · exact absurd hi (by simp)

theorem redP_vars (V : NPVerifier L) (n : ℕ) :
    ∀ c ∈ redP V n, ∀ l ∈ c, l.1 < redK V n := by
  intro c hc l hl
  rw [redP, List.mem_append] at hc
  rcases hc with hc | hc
  · have := tseitinP_vars (V.wf n) (redMode_none V n) c hc l hl
    simp only [redK]
    omega
  · split at hc
    · simp only [List.mem_singleton] at hc
      subst hc
      exact absurd hl (by simp)
    · simp only [List.mem_singleton] at hc
      subst hc
      simp only [List.mem_singleton] at hl
      subst hl
      simp only [gv, redK]
      omega

theorem red_eq (V : NPVerifier L) (x : List Bool) :
    red V x = encodeCNF (redK V x.length) (PCnf.inst x (redP V x.length)) := by
  rw [red, redBits, encodeCNFP_eval _ _ _ (redP_consistent V x.length)]

/-! ### Correctness of the reduction -/

theorem circ_eval_nil (X : ℕ → Bool) : Circ.eval [] X = false := by
  simp [Circ.eval, vals, valsAux]

theorem inst_redP (V : NPVerifier L) (x : List Bool) (n : ℕ) :
    PCnf.inst x (redP V n) =
      tseitin (modeVal (redMode V n) x) (V.circ n) ++
        (if (V.circ n).length = 0 then [([] : CNF.Clause ℕ)]
          else [[(gv ((V.circ n).length - 1), true)]]) := by
  rw [redP, inst_append, inst_tseitinP]
  congr 1
  split <;> simp [PCnf.inst, PClause.inst, ProjBit.eval]

/-- The key correctness property of the reduction. -/
theorem red_spec (V : NPVerifier L) (x : List Bool) :
    (∃ a : ℕ → Bool, CNF.eval a (PCnf.inst x (redP V x.length)) = true) ↔ x ∈ L := by
  set n := x.length with hn
  set m := V.wlen n with hm
  set gs := V.circ n with hgs
  set fixed := modeVal (redMode V n) x with hfixed
  have hfix : ∀ i, fixed i =
      if i < n then some (x.getD i false) else if i < n + m then none else some false := by
    intro i
    simp only [hfixed, modeVal, redMode, ← hm]
    split
    · simp [ProjBit.eval]
    · split <;> simp [ProjBit.eval]
  rw [inst_redP, V.spec x, ← hn, ← hm, ← hgs]
  by_cases hlen : gs.length = 0
  · have hgsnil : gs = [] := List.eq_nil_of_length_eq_zero hlen
    constructor
    · rintro ⟨a, ha⟩
      rw [if_pos hlen, hgsnil] at ha
      simp only [tseitin, List.zipIdx_nil, List.flatMap_nil, List.nil_append] at ha
      simp [CNF.eval, CNF.Clause.eval] at ha
    · rintro ⟨w, _, hw⟩
      rw [hgsnil, circ_eval_nil] at hw
      exact absurd hw (by simp)
  · rw [if_neg hlen]
    constructor
    · rintro ⟨a, ha⟩
      rw [CNF.eval_append] at ha
      have ha1 : CNF.eval a (tseitin fixed gs) = true := by
        revert ha; cases CNF.eval a (tseitin fixed gs) <;> simp
      have ha2 : a (gv (gs.length - 1)) = true := by
        have : CNF.eval a [[(gv (gs.length - 1), true)]] = true := by
          revert ha; cases CNF.eval a [[(gv (gs.length - 1), true)]] <;> simp
        simpa [CNF.eval, CNF.Clause.eval] using this
      set X := inputOf fixed a with hX
      have hsound := tseitin_sound (V.wf n) ha1
      rw [← hgs] at hsound
      have hacc : Circ.eval gs X = true := by
        rw [Circ.eval, ← hsound (gs.length - 1) (by omega)]
        exact ha2
      refine ⟨(List.range m).map (fun i => X (n + i)), by simp, ?_⟩
      have hassign : assign x ((List.range m).map (fun i => X (n + i))) = X := by
        funext i
        rcases lt_or_ge i n with hi | hi
        · simp only [assign, ← hn, if_pos hi]
          rw [hX, inputOf, hfix i, if_pos hi]
          simp
        · rcases lt_or_ge i (n + m) with hi2 | hi2
          · have hidx : i - n < m := by omega
            simp only [assign, ← hn]
            rw [if_neg (show ¬ i < n by omega)]
            rw [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_range (by simpa using hidx)]
            simp only [Option.map_some, Option.getD_some]
            congr 1
            omega
          · simp only [assign, ← hn]
            rw [if_neg (show ¬ i < n by omega)]
            rw [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_none (l := List.range m) (by simp; omega)]
            rw [hX, inputOf, hfix i, if_neg (by omega), if_neg (by omega)]
            simp
      rw [hassign]
      exact hacc
    · rintro ⟨w, hwlen, hw⟩
      set X := assign x w with hXdef
      have hx : ∀ i b, fixed i = some b → X i = b := by
        intro i b hib
        rw [hfix i] at hib
        rcases lt_or_ge i n with hi | hi
        · rw [if_pos hi] at hib
          have : b = x.getD i false := by simpa using hib.symm
          rw [this, hXdef, assign, if_pos (by omega)]
        · rw [if_neg (by omega)] at hib
          rcases lt_or_ge i (n + m) with hi2 | hi2
          · rw [if_pos hi2] at hib; exact absurd hib (by simp)
          · rw [if_neg (by omega)] at hib
            have hb : b = false := by simpa using hib.symm
            rw [hb, hXdef, assign, if_neg (by omega)]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            simp
      refine ⟨assignOf gs X, ?_⟩
      rw [CNF.eval_append]
      have h1 : CNF.eval (assignOf gs X) (tseitin fixed gs) = true :=
        tseitin_complete (V.wf n) hx
      have h2 : CNF.eval (assignOf gs X) [[(gv (gs.length - 1), true)]] = true := by
        have hval : assignOf gs X (gv (gs.length - 1)) = true := by
          rw [assignOf_gv]; exact hw
        simp [CNF.eval, CNF.Clause.eval, hval]
      rw [h1, h2]
      rfl

/-- The reduction is correct. -/
theorem red_mem_SAT (V : NPVerifier L) (x : List Bool) : x ∈ L ↔ red V x ∈ SATlang := by
  rw [← red_spec V x, red_eq, SATlang, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by
      rw [eval_decode_encode (by simp [redK])
        (by simpa using redP_length V x.length) (inst_vars (redP_vars V x.length)) a]
      exact ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [eval_decode_encode (by simp [redK])
      (by simpa using redP_length V x.length) (inst_vars (redP_vars V x.length)) a] at ha
    exact ha

theorem redK_poly (V : NPVerifier L) : Poly (redK V) := by
  have h1 : Poly (fun n => (V.circ n).length) := V.size_poly
  have h2 : Poly V.wlen := V.wlen_poly
  exact (((Poly.const 5).mul h1).add (((Poly.const 2).mul (Poly.id.add h2)))).add (Poly.const 2)

/-- The reduction is a projection with polynomially many output bits. -/
theorem red_isProjection (V : NPVerifier L) : IsProjectionReduction (red V) := by
  refine ⟨redBits V, fun x => rfl, ?_⟩
  refine Poly.mono (g := fun n => 2 * redK V n * redK V n) ?_ ?_
  · exact ((Poly.const 2).mul (redK_poly V)).mul (redK_poly V)
  · intro n
    simp [redBits, encodeCNFP]

end Frontier

import Mathlib
import RequestProject.Tseitin

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Encoding CNF formulas as bit strings

A bit string of length `ℓ` is read as a `k × k` occurrence matrix of literals, where
`k = ⌊√(ℓ/2)⌋`: the two bits at positions `bitIdx k i j true` and `bitIdx k i j false`
say whether the literals `(j, true)` and `(j, false)` occur in clause `i`.
So a bit string always denotes a CNF formula with `k` clauses over the `k` variables
`0, …, k-1`.

Conversely `encodeCNF k f` writes a formula with at most `k` clauses over the variables
`0, …, k-1` as a bit string of length `2 * k * k`; rows beyond the clauses of `f` are
filled with all-ones rows, i.e. with tautological clauses.
-/

namespace Frontier

open Std.Sat

/-- Position of the bit recording the occurrence of the literal `(j, b)` in clause `i`. -/
def bitIdx (k i j : ℕ) (b : Bool) : ℕ := 2 * (i * k + j) + (if b then 0 else 1)

/-- Clause number `i` of the formula denoted by the bit string `s` (with `k` variables). -/
def decodeClause (s : List Bool) (k i : ℕ) : CNF.Clause ℕ :=
  ((List.range k).flatMap (fun j => [((j : ℕ), true), ((j : ℕ), false)])).filter
    (fun l => s.getD (bitIdx k i l.1 l.2) false)

/-- The CNF formula denoted by a bit string. -/
def decodeCNF (s : List Bool) : CNF ℕ :=
  (List.range (Nat.sqrt (s.length / 2))).map (decodeClause s (Nat.sqrt (s.length / 2)))

/-- The bit at position `t` of the encoding of `f`. -/
def encodeBit (k : ℕ) (f : CNF ℕ) (t : ℕ) : Bool :=
  (f[t / (2 * k)]?).elim true
    (fun c => decide (((t % (2 * k)) / 2, decide ((t % (2 * k)) % 2 = 0)) ∈ c))

/-- Encoding of a CNF formula (with at most `k` clauses over the variables `< k`)
as a bit string of length `2 * k * k`. -/
def encodeCNF (k : ℕ) (f : CNF ℕ) : List Bool := (List.range (2 * k * k)).map (encodeBit k f)

@[simp] theorem length_encodeCNF (k : ℕ) (f : CNF ℕ) : (encodeCNF k f).length = 2 * k * k := by
  simp [encodeCNF]

theorem sqrt_encode (k : ℕ) (f : CNF ℕ) : Nat.sqrt ((encodeCNF k f).length / 2) = k := by
  rw [length_encodeCNF]
  have h : 2 * k * k = 2 * (k * k) := by ring
  rw [h, Nat.mul_div_cancel_left _ (by norm_num), Nat.sqrt_eq]

theorem bitIdx_lt {k i j : ℕ} (b : Bool) (hi : i < k) (hj : j < k) : bitIdx k i j b < 2 * k * k := by
  have h1 : i * k + j < k * k := by
    calc i * k + j < i * k + k := by omega
      _ = (i + 1) * k := by ring
      _ ≤ k * k := Nat.mul_le_mul_right k (by omega)
  have h2 : (if b then 0 else 1) ≤ 1 := by cases b <;> simp
  have h3 : 2 * k * k = 2 * (k * k) := by ring
  simp only [bitIdx, h3]
  omega

theorem encodeCNF_getD (k : ℕ) (f : CNF ℕ) {t : ℕ} (ht : t < 2 * k * k) :
    (encodeCNF k f).getD t false = encodeBit k f t := by
  rw [List.getD_eq_getElem?_getD, encodeCNF, List.getElem?_map,
    List.getElem?_range (by simpa using ht)]
  simp

theorem encodeBit_bitIdx (k : ℕ) (f : CNF ℕ) {i j : ℕ} (b : Bool) (hj : j < k) :
    encodeBit k f (bitIdx k i j b) = (f[i]?).elim true (fun c => decide ((j, b) ∈ c)) := by
  have hk : 0 < 2 * k := by omega
  obtain ⟨e, he, he1, hbe⟩ :
      ∃ e : ℕ, (if b then 0 else 1) = e ∧ e ≤ 1 ∧ decide ((2 * j + e) % 2 = 0) = b := by
    cases b
    · exact ⟨1, rfl, le_refl 1, by simp⟩
    · exact ⟨0, rfl, Nat.zero_le 1, by simp⟩
  have hsmall : 2 * j + e < 2 * k := by omega
  have hform : bitIdx k i j b = 2 * k * i + (2 * j + e) := by
    simp only [bitIdx, he]; ring
  have hdiv : bitIdx k i j b / (2 * k) = i := by
    rw [hform, Nat.mul_add_div hk, Nat.div_eq_of_lt hsmall]
    simp
  have hmod : bitIdx k i j b % (2 * k) = 2 * j + e := by
    rw [hform, Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]
  have hj2 : (2 * j + e) / 2 = j := by omega
  rw [encodeBit, hdiv, hmod, hj2, hbe]

/-- Two clauses with the same literals have the same value. -/
theorem clause_eval_congr (a : ℕ → Bool) {c₁ c₂ : CNF.Clause ℕ} (h : ∀ l, l ∈ c₁ ↔ l ∈ c₂) :
    CNF.Clause.eval a c₁ = CNF.Clause.eval a c₂ := by
  rw [Bool.eq_iff_iff]
  simp only [CNF.Clause.eval, List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hv⟩; exact ⟨l, (h l).mp hl, hv⟩
  · rintro ⟨l, hl, hv⟩; exact ⟨l, (h l).mpr hl, hv⟩

theorem mem_decodeClause {s : List Bool} {k i j : ℕ} {b : Bool} :
    (j, b) ∈ decodeClause s k i ↔ j < k ∧ s.getD (bitIdx k i j b) false = true := by
  simp only [decodeClause, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨⟨j', hj', hmem⟩, hbit⟩
    have hjj : j' = j := by
      rcases hmem with h | h <;> · injection h with h1 _; exact h1.symm
    subst hjj
    exact ⟨hj', hbit⟩
  · rintro ⟨hj, hb⟩
    refine ⟨⟨j, hj, ?_⟩, hb⟩
    cases b
    · right; rfl
    · left; rfl

/-- Reading back an encoded formula gives a formula with the same value under every
assignment. -/
theorem eval_decode_encode {k : ℕ} {f : CNF ℕ} (hk : 0 < k) (hlen : f.length ≤ k)
    (hvar : ∀ c ∈ f, ∀ l ∈ c, l.1 < k) (a : ℕ → Bool) :
    CNF.eval a (decodeCNF (encodeCNF k f)) = CNF.eval a f := by
  set s := encodeCNF k f with hs
  have hdec : decodeCNF s = (List.range k).map (decodeClause s k) := by
    rw [decodeCNF, hs, sqrt_encode]
  -- value of a decoded clause
  have hclause : ∀ i, i < k → ∀ c, f[i]? = some c →
      CNF.Clause.eval a (decodeClause s k i) = CNF.Clause.eval a c := by
    intro i hi c hc
    refine clause_eval_congr a ?_
    rintro ⟨j, b⟩
    rw [mem_decodeClause]
    constructor
    · rintro ⟨hj, hb⟩
      rw [hs, encodeCNF_getD k f (bitIdx_lt b hi hj), encodeBit_bitIdx k f b hj, hc] at hb
      simpa using hb
    · intro hmem
      have hjk : j < k := hvar c (List.mem_of_getElem? hc) (j, b) hmem
      refine ⟨hjk, ?_⟩
      rw [hs, encodeCNF_getD k f (bitIdx_lt b hi hjk), encodeBit_bitIdx k f b hjk, hc]
      simpa using hmem
  -- a padding row is a tautology
  have hpad : ∀ i, i < k → f[i]? = none → CNF.Clause.eval a (decodeClause s k i) = true := by
    intro i hi hc
    have hmem : ∀ b : Bool, (0, b) ∈ decodeClause s k i := by
      intro b
      rw [mem_decodeClause]
      refine ⟨hk, ?_⟩
      rw [hs, encodeCNF_getD k f (bitIdx_lt b hi hk), encodeBit_bitIdx k f b hk, hc]
      simp
    simp only [CNF.Clause.eval, List.any_eq_true]
    exact ⟨(0, a 0), hmem (a 0), by simp⟩
  rw [Bool.eq_iff_iff, eval_eq_true_iff, eval_eq_true_iff, hdec]
  constructor
  · intro h c hc
    obtain ⟨i, hi, hget⟩ : ∃ i, i < f.length ∧ f[i]? = some c := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp hc
      exact ⟨i, hi.1, by rw [List.getElem?_eq_getElem hi.1, hi.2]⟩
    have hik : i < k := lt_of_lt_of_le hi hlen
    rw [← hclause i hik c hget]
    exact h _ (List.mem_map_of_mem (by simpa using hik))
  · intro h c hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    cases hget : f[i]? with
    | none => exact hpad i hi hget
    | some c' =>
        rw [hclause i hi c' hget]
        exact h c' (List.mem_of_getElem? hget)

/-! ### Parametric encoding

For the reduction we need the bits of the encoding to depend on the input word only
through single bits ("projections"). -/

/-- The polarity attached to the variable `j` in a parametric clause, if any. -/
def lookupVar (c : PClause) (j : ℕ) : Option ProjBit :=
  (c.find? (fun p => decide (p.1 = j))).map (fun p => p.2)

/-- `matchBit p b` evaluates to `true` exactly when `p` evaluates to `b`. -/
def matchBit (p : ProjBit) (b : Bool) : ProjBit :=
  match p with
  | .cst c => .cst (c == b)
  | .pos i => if b then .pos i else .neg i
  | .neg i => if b then .neg i else .pos i

theorem matchBit_eval (x : List Bool) (p : ProjBit) (b : Bool) :
    (matchBit p b).eval x = (p.eval x == b) := by
  cases p <;> cases b <;> simp [matchBit, ProjBit.eval]

/-- A parametric clause is consistent if a variable occurs with only one polarity. -/
def PClause.Consistent (c : PClause) : Prop :=
  ∀ p ∈ c, ∀ q ∈ c, p.1 = q.1 → p.2 = q.2

theorem mem_inst_iff (x : List Bool) (c : PClause) (j : ℕ) (b : Bool)
    (hcon : PClause.Consistent c) :
    ((j, b) ∈ PClause.inst x c) ↔
      (match lookupVar c j with
        | some p => p.eval x = b
        | none => False) := by
  simp only [PClause.inst, List.mem_map]
  cases hl : lookupVar c j with
  | none =>
      simp only [iff_false]
      rintro ⟨q, hq, hqe⟩
      have hq1 : q.1 = j := by simpa using congrArg Prod.fst hqe
      rw [lookupVar] at hl
      cases hf : c.find? (fun p => decide (p.1 = j)) with
      | none =>
          have := List.find?_eq_none.mp hf q hq
          simp [hq1] at this
      | some p => rw [hf] at hl; simp at hl
  | some p =>
      rw [lookupVar] at hl
      cases hf : c.find? (fun p => decide (p.1 = j)) with
      | none => rw [hf] at hl; simp at hl
      | some q =>
          rw [hf] at hl
          simp only [Option.map_some] at hl
          have hqmem : q ∈ c := List.mem_of_find?_eq_some hf
          have hq1 : q.1 = j := by simpa using List.find?_some hf
          have hqp : q.2 = p := Option.some.inj hl
          subst hqp
          constructor
          · rintro ⟨r, hr, hre⟩
            have hr1 : r.1 = j := by simpa using congrArg Prod.fst hre
            have hr2 : r.2 = q.2 := hcon r hr q hqmem (by rw [hr1, hq1])
            have : r.2.eval x = b := by simpa using congrArg Prod.snd hre
            rwa [hr2] at this
          · intro hb
            exact ⟨q, hqmem, by rw [hq1, hb]⟩

/-- The projection bit recording the occurrence of the literal `(j, b)` in the
parametric clause `c`. -/
def clauseBitP (c : PClause) (j : ℕ) (b : Bool) : ProjBit :=
  match lookupVar c j with
  | some p => matchBit p b
  | none => .cst false

theorem clauseBitP_eval (x : List Bool) (c : PClause) (j : ℕ) (b : Bool)
    (hcc : PClause.Consistent c) :
    (clauseBitP c j b).eval x = decide ((j, b) ∈ PClause.inst x c) := by
  have hmem := mem_inst_iff x c j b hcc
  rw [clauseBitP]
  cases hl : lookupVar c j with
  | none =>
      rw [hl] at hmem
      simp only [ProjBit.eval]
      simp [hmem]
  | some p =>
      rw [hl] at hmem
      rw [matchBit_eval]
      simp only [hmem]
      cases ProjBit.eval x p <;> cases b <;> simp

/-- The parametric version of `encodeBit`. -/
def encodeBitP (k : ℕ) (F : PCnf) (t : ℕ) : ProjBit :=
  (F[t / (2 * k)]?).elim (.cst true)
    (fun c => clauseBitP c ((t % (2 * k)) / 2) (decide ((t % (2 * k)) % 2 = 0)))

/-- The parametric version of `encodeCNF`. -/
def encodeCNFP (k : ℕ) (F : PCnf) : List ProjBit := (List.range (2 * k * k)).map (encodeBitP k F)

theorem encodeBitP_aux (x : List Bool) (F : PCnf) (i j : ℕ) (b : Bool)
    (hcon : ∀ c ∈ F, PClause.Consistent c) :
    ProjBit.eval x ((F[i]?).elim (ProjBit.cst true) (fun c => clauseBitP c j b))
      = ((PCnf.inst x F)[i]?).elim true (fun c => decide ((j, b) ∈ c)) := by
  rw [PCnf.inst, List.getElem?_map]
  cases hF : F[i]? with
  | none => simp [ProjBit.eval]
  | some c =>
      have hcc := hcon c (List.mem_of_getElem? hF)
      simp only [Option.elim_some, Option.map_some]
      exact clauseBitP_eval x c j b hcc

theorem encodeCNFP_eval (k : ℕ) (F : PCnf) (x : List Bool)
    (hcon : ∀ c ∈ F, PClause.Consistent c) :
    (encodeCNFP k F).map (fun p => p.eval x) = encodeCNF k (PCnf.inst x F) := by
  simp only [encodeCNFP, encodeCNF, List.map_map]
  refine List.map_congr_left ?_
  intro t _
  simp only [Function.comp_apply, encodeBitP, encodeBit]
  exact encodeBitP_aux x F _ _ _ hcon

end Frontier

import Mathlib
import RequestProject.CookLevin

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
import RequestProject.Circuit

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Tseitin transformation

Given a circuit `gs`, we build a CNF formula whose satisfying assignments are exactly the
accepting computations of the circuit.  Some of the circuit's input variables may be
*fixed* to prescribed truth values; the remaining ones stay free.

We use `Std.Sat.CNF ℕ` as the type of CNF formulas: a clause is a list of literals
`(v, b)`, satisfied by the assignment `a` when `a v = b`.

Variables of the produced formula: `gv j = 2 * j` stands for the value of gate `j`,
and `iv i = 2 * i + 1` stands for the value of the (free) input variable `i`.
-/

namespace Frontier

open Std.Sat

/-- A bit that either is a constant or reads (the negation of) one bit of the input word.
These are used to describe *projection* reductions. -/
inductive ProjBit where
  | cst (b : Bool)
  | pos (i : ℕ)
  | neg (i : ℕ)
  deriving DecidableEq, Repr

/-- Value of a projection bit on the input word `x`. -/
def ProjBit.eval (x : List Bool) : ProjBit → Bool
  | .cst b => b
  | .pos i => x.getD i false
  | .neg i => !(x.getD i false)

/-- A clause whose literal polarities may depend on the input word. -/
abbrev PClause := List (ℕ × ProjBit)

/-- A CNF whose literal polarities may depend on the input word. -/
abbrev PCnf := List PClause

/-- Instantiate a parametric clause at the input word `x`. -/
def PClause.inst (x : List Bool) (c : PClause) : CNF.Clause ℕ :=
  c.map (fun p => (p.1, p.2.eval x))

/-- Instantiate a parametric CNF at the input word `x`. -/
def PCnf.inst (x : List Bool) (f : PCnf) : CNF ℕ := f.map (PClause.inst x)

/-- CNF variable holding the value of gate `j`. -/
def gv (j : ℕ) : ℕ := 2 * j

/-- CNF variable holding the value of the free circuit input `i`. -/
def iv (i : ℕ) : ℕ := 2 * i + 1

theorem gv_ne_iv (j i : ℕ) : gv j ≠ iv i := by
  simp [gv, iv]; omega

/-- The clauses defining the value of the gate at position `j`. -/
def gateClauses (fixed : ℕ → Option Bool) (j : ℕ) : Gate → CNF ℕ
  | .inp i =>
      match fixed i with
      | some b => [[(gv j, b)]]
      | none => [[(gv j, false), (iv i, true)], [(gv j, true), (iv i, false)]]
  | .const b => [[(gv j, b)]]
  | .neg k => [[(gv j, false), (gv k, false)], [(gv j, true), (gv k, true)]]
  | .conj k l =>
      [[(gv j, false), (gv k, true)], [(gv j, false), (gv l, true)],
        [(gv j, true), (gv k, false), (gv l, false)]]
  | .disj k l =>
      [[(gv j, true), (gv k, false)], [(gv j, true), (gv l, false)],
        [(gv j, false), (gv k, true), (gv l, true)]]

/-- The Tseitin CNF of a circuit, with some inputs fixed. -/
def tseitin (fixed : ℕ → Option Bool) (gs : Circ) : CNF ℕ :=
  gs.zipIdx.flatMap (fun p => gateClauses fixed p.2 p.1)

/-- Parametric version of `gateClauses`. -/
def gateClausesP (mode : ℕ → Option ProjBit) (j : ℕ) : Gate → PCnf
  | .inp i =>
      match mode i with
      | some p => [[(gv j, p)]]
      | none => [[(gv j, .cst false), (iv i, .cst true)], [(gv j, .cst true), (iv i, .cst false)]]
  | .const b => [[(gv j, .cst b)]]
  | .neg k => [[(gv j, .cst false), (gv k, .cst false)], [(gv j, .cst true), (gv k, .cst true)]]
  | .conj k l =>
      [[(gv j, .cst false), (gv k, .cst true)], [(gv j, .cst false), (gv l, .cst true)],
        [(gv j, .cst true), (gv k, .cst false), (gv l, .cst false)]]
  | .disj k l =>
      [[(gv j, .cst true), (gv k, .cst false)], [(gv j, .cst true), (gv l, .cst false)],
        [(gv j, .cst false), (gv k, .cst true), (gv l, .cst true)]]

/-- Parametric version of `tseitin`. -/
def tseitinP (mode : ℕ → Option ProjBit) (gs : Circ) : PCnf :=
  gs.zipIdx.flatMap (fun p => gateClausesP mode p.2 p.1)

/-- The truth values that a `mode` prescribes on the input word `x`. -/
def modeVal (mode : ℕ → Option ProjBit) (x : List Bool) : ℕ → Option Bool :=
  fun i => (mode i).map (fun p => p.eval x)

theorem gateClausesP_inst (mode : ℕ → Option ProjBit) (x : List Bool) (j : ℕ) (g : Gate) :
    (gateClausesP mode j g).map (PClause.inst x) = gateClauses (modeVal mode x) j g := by
  cases g with
  | inp i =>
      cases hm : mode i with
      | none => simp [gateClausesP, gateClauses, modeVal, hm, PClause.inst, ProjBit.eval]
      | some p => simp [gateClausesP, gateClauses, modeVal, hm, PClause.inst, ProjBit.eval]
  | const b => simp [gateClausesP, gateClauses, PClause.inst, ProjBit.eval]
  | neg k => simp [gateClausesP, gateClauses, PClause.inst, ProjBit.eval]
  | conj k l => simp [gateClausesP, gateClauses, PClause.inst, ProjBit.eval]
  | disj k l => simp [gateClausesP, gateClauses, PClause.inst, ProjBit.eval]

theorem inst_tseitinP (mode : ℕ → Option ProjBit) (x : List Bool) (gs : Circ) :
    PCnf.inst x (tseitinP mode gs) = tseitin (modeVal mode x) gs := by
  simp only [PCnf.inst, tseitinP, tseitin, List.map_flatMap]
  apply List.flatMap_congr
  intro p _
  exact gateClausesP_inst mode x p.2 p.1

/-! ### Correctness of the Tseitin transformation -/

/-- The input assignment induced by a CNF assignment. -/
def inputOf (fixed : ℕ → Option Bool) (a : ℕ → Bool) : ℕ → Bool :=
  fun i => (fixed i).getD (a (iv i))

/-- The CNF assignment induced by an input assignment. -/
def assignOf (gs : Circ) (x : ℕ → Bool) : ℕ → Bool :=
  fun v => if v % 2 = 0 then (vals x gs).getD (v / 2) false else x (v / 2)

@[simp] theorem assignOf_gv (gs : Circ) (x : ℕ → Bool) (j : ℕ) :
    assignOf gs x (gv j) = (vals x gs).getD j false := by
  simp [assignOf, gv]

@[simp] theorem assignOf_iv (gs : Circ) (x : ℕ → Bool) (i : ℕ) :
    assignOf gs x (iv i) = x i := by
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [assignOf, iv, h1, h2]

theorem mem_tseitin {fixed : ℕ → Option Bool} {gs : Circ} {c : CNF.Clause ℕ}
    (hc : c ∈ tseitin fixed gs) : ∃ j g, gs[j]? = some g ∧ c ∈ gateClauses fixed j g := by
  rw [tseitin, List.mem_flatMap] at hc
  obtain ⟨⟨g, j⟩, hmem, hc⟩ := hc
  exact ⟨j, g, List.mem_zipIdx_iff_getElem?.mp hmem, hc⟩

theorem clause_mem_tseitin {fixed : ℕ → Option Bool} {gs : Circ} {c : CNF.Clause ℕ}
    {j : ℕ} {g : Gate} (hg : gs[j]? = some g) (hc : c ∈ gateClauses fixed j g) :
    c ∈ tseitin fixed gs := by
  rw [tseitin, List.mem_flatMap]
  exact ⟨(g, j), List.mem_zipIdx_iff_getElem?.mpr (by simpa using hg), hc⟩

theorem eval_eq_true_iff (a : ℕ → Bool) (f : CNF ℕ) :
    CNF.eval a f = true ↔ ∀ c ∈ f, CNF.Clause.eval a c = true := by
  simp [CNF.eval, List.all_eq_true]

/-- **Soundness**: a satisfying assignment of the Tseitin CNF encodes the run of the
circuit on the input word it describes. -/
theorem tseitin_sound {fixed : ℕ → Option Bool} {gs : Circ} (hwf : Circ.WF gs) {a : ℕ → Bool}
    (ha : CNF.eval a (tseitin fixed gs) = true) :
    ∀ j, j < gs.length → a (gv j) = (vals (inputOf fixed a) gs).getD j false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem hj⟩
    have hval : (vals (inputOf fixed a) gs).getD j false
        = Gate.eval (inputOf fixed a) (vals (inputOf fixed a) gs) g :=
      vals_getD_eq _ hwf hg
    have hsat : ∀ c ∈ gateClauses fixed j g, CNF.Clause.eval a c = true := fun c hc =>
      (eval_eq_true_iff a _).mp ha c (clause_mem_tseitin hg hc)
    rw [hval]
    cases g with
    | inp i =>
        cases hf : fixed i with
        | some b =>
            have h1 := hsat [(gv j, b)] (by simp [gateClauses, hf])
            simp [CNF.Clause.eval] at h1
            simp [Gate.eval, inputOf, hf, h1]
        | none =>
            have h1 := hsat [(gv j, false), (iv i, true)] (by simp [gateClauses, hf])
            have h2 := hsat [(gv j, true), (iv i, false)] (by simp [gateClauses, hf])
            simp [CNF.Clause.eval] at h1 h2
            simp only [Gate.eval, inputOf, hf, Option.getD_none]
            revert h1 h2
            cases a (gv j) <;> cases a (iv i) <;> simp
    | const b =>
        have h1 := hsat [(gv j, b)] (by simp [gateClauses])
        simp [CNF.Clause.eval] at h1
        simp [Gate.eval, h1]
    | neg k =>
        have hk : k < j := hwf j _ hg
        have hk2 := ih k hk (by omega)
        have h1 := hsat [(gv j, false), (gv k, false)] (by simp [gateClauses])
        have h2 := hsat [(gv j, true), (gv k, true)] (by simp [gateClauses])
        simp [CNF.Clause.eval] at h1 h2
        simp only [Gate.eval, ← hk2]
        revert h1 h2
        cases a (gv j) <;> cases a (gv k) <;> simp
    | conj k l =>
        obtain ⟨hk, hl⟩ : k < j ∧ l < j := hwf j _ hg
        have hk2 := ih k hk (by omega)
        have hl2 := ih l hl (by omega)
        have h1 := hsat [(gv j, false), (gv k, true)] (by simp [gateClauses])
        have h2 := hsat [(gv j, false), (gv l, true)] (by simp [gateClauses])
        have h3 := hsat [(gv j, true), (gv k, false), (gv l, false)] (by simp [gateClauses])
        simp [CNF.Clause.eval] at h1 h2 h3
        simp only [Gate.eval, ← hk2, ← hl2]
        revert h1 h2 h3
        cases a (gv j) <;> cases a (gv k) <;> cases a (gv l) <;> simp
    | disj k l =>
        obtain ⟨hk, hl⟩ : k < j ∧ l < j := hwf j _ hg
        have hk2 := ih k hk (by omega)
        have hl2 := ih l hl (by omega)
        have h1 := hsat [(gv j, true), (gv k, false)] (by simp [gateClauses])
        have h2 := hsat [(gv j, true), (gv l, false)] (by simp [gateClauses])
        have h3 := hsat [(gv j, false), (gv k, true), (gv l, true)] (by simp [gateClauses])
        simp [CNF.Clause.eval] at h1 h2 h3
        simp only [Gate.eval, ← hk2, ← hl2]
        revert h1 h2 h3
        cases a (gv j) <;> cases a (gv k) <;> cases a (gv l) <;> simp

/-- **Completeness**: the run of the circuit on an input word compatible with the fixed
values yields a satisfying assignment of the Tseitin CNF. -/
theorem tseitin_complete {fixed : ℕ → Option Bool} {gs : Circ} (hwf : Circ.WF gs)
    {x : ℕ → Bool} (hx : ∀ i b, fixed i = some b → x i = b) :
    CNF.eval (assignOf gs x) (tseitin fixed gs) = true := by
  rw [eval_eq_true_iff]
  intro c hc
  obtain ⟨j, g, hg, hc⟩ := mem_tseitin hc
  have hval : (vals x gs).getD j false = Gate.eval x (vals x gs) g := vals_getD_eq x hwf hg
  cases g with
  | inp i =>
      cases hf : fixed i with
      | some b =>
          simp only [gateClauses, hf, List.mem_singleton] at hc
          subst hc
          have hxb : x i = b := hx i b hf
          simp only [Gate.eval] at hval
          simp only [CNF.Clause.eval, List.any_cons, List.any_nil, assignOf_gv, hval, hxb]
          simp
      | none =>
          simp only [gateClauses, hf, List.mem_cons, List.not_mem_nil, or_false] at hc
          simp only [Gate.eval] at hval
          rcases hc with rfl | rfl <;>
            rcases Bool.eq_false_or_eq_true (x i) with hxi | hxi <;>
            simp only [CNF.Clause.eval, List.any_cons, List.any_nil, assignOf_gv, assignOf_iv,
              hval, hxi] <;> rfl
  | const b =>
      simp only [gateClauses, List.mem_singleton] at hc
      subst hc
      simp only [Gate.eval] at hval
      simp only [CNF.Clause.eval, List.any_cons, List.any_nil, assignOf_gv, hval]
      simp
  | neg k =>
      simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      simp only [Gate.eval] at hval
      rcases hc with rfl | rfl <;>
        rcases Bool.eq_false_or_eq_true ((vals x gs).getD k false) with hk | hk <;>
        simp only [CNF.Clause.eval, List.any_cons, List.any_nil, assignOf_gv, hval, hk] <;> rfl
  | conj k l =>
      simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      simp only [Gate.eval] at hval
      rcases hc with rfl | rfl | rfl <;>
        rcases Bool.eq_false_or_eq_true ((vals x gs).getD k false) with hk | hk <;>
        rcases Bool.eq_false_or_eq_true ((vals x gs).getD l false) with hl | hl <;>
        simp only [CNF.Clause.eval, List.any_cons, List.any_nil, assignOf_gv, hval, hk, hl] <;> rfl
  | disj k l =>
      simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      simp only [Gate.eval] at hval
      rcases hc with rfl | rfl | rfl <;>
        rcases Bool.eq_false_or_eq_true ((vals x gs).getD k false) with hk | hk <;>
        rcases Bool.eq_false_or_eq_true ((vals x gs).getD l false) with hl | hl <;>
        simp only [CNF.Clause.eval, List.any_cons, List.any_nil, assignOf_gv, hval, hk, hl] <;> rfl

end Frontier

