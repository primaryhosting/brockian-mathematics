import RequestProject.Encode

/-!
# The class NP, via polynomial-size verifier circuits

A language `L ⊆ {0,1}*` is in `NP` when there is a family of Boolean circuits
`circ n`, of size polynomial in `n`, such that `x ∈ L` iff some setting of the
"free" inputs (the inputs of index `≥ |x|`, i.e. the witness) makes `circ |x|`
accept the string `x`.

Note that no bound on the witness has to be imposed: a circuit of size `s` reads
at most `s` of its inputs, so the witness is automatically of polynomial length.
-/

namespace Frontier

/-- A polynomial-size verifier-circuit family witnessing that `L` is in `NP`. -/
structure NPVerifier (L : List Bool → Prop) where
  /-- The verifier circuit for inputs of length `n`. -/
  circ : ℕ → Circuit
  /-- Coefficient of the polynomial size bound. -/
  coeff : ℕ
  /-- Exponent of the polynomial size bound. -/
  exponent : ℕ
  /-- The circuit family has polynomial size. -/
  size_le : ∀ n, (circ n).length ≤ coeff * (n + 1) ^ exponent
  /-- `x ∈ L` iff some witness makes the verifier accept. -/
  spec : ∀ x : List Bool, L x ↔ ∃ w : ℕ → Bool, evalC (circ x.length) (extend x w) = true

end Frontier

import Mathlib

/-!
# Basic objects: CNF formulas and Boolean circuits

This file sets up the two computational objects used in the Cook–Levin development:

* CNF formulas over natural-number variables, and their satisfiability;
* Boolean circuits, presented as straight-line programs with *relative*
  back-references (a gate at position `i` may refer to the gate `d` steps
  before it).  Out-of-range references evaluate to `false`, so evaluation is
  total and no well-formedness side condition is ever needed.
* Boolean *expressions* (trees) together with a compiler into circuits.  This
  is only used as a convenient way of building concrete circuits.
-/

namespace Frontier

/-! ### CNF formulas -/

/-- A literal is a variable index together with the polarity it is asserted with. -/
abbrev Lit := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF := List Clause

/-- Is the literal `l` true under the assignment `a`? -/
def satLit (a : ℕ → Bool) (l : Lit) : Bool := a l.1 == l.2

/-- Is the clause `c` true under the assignment `a`? -/
def satClause (a : ℕ → Bool) (c : Clause) : Bool := c.any (satLit a)

/-- Is the CNF formula `f` true under the assignment `a`? -/
def satCNF (a : ℕ → Bool) (f : CNF) : Bool := f.all (satClause a)

/-- Satisfiability of a CNF formula. -/
def Sat (f : CNF) : Prop := ∃ a : ℕ → Bool, satCNF a f = true

@[simp] lemma satCNF_append (a : ℕ → Bool) (f g : CNF) :
    satCNF a (f ++ g) = (satCNF a f && satCNF a g) := by
  simp [satCNF]

@[simp] lemma satClause_cons (a : ℕ → Bool) (l : Lit) (c : Clause) :
    satClause a (l :: c) = (satLit a l || satClause a c) := by
  simp [satClause]

@[simp] lemma satClause_nil (a : ℕ → Bool) : satClause a [] = false := rfl

/-! ### Circuits -/

/-- A gate of a straight-line Boolean program.  References `d` are *relative*:
the gate at position `i` referring to `d` reads the value produced at position
`i - 1 - d`.  If `d ≥ i` the reference is out of range and reads `false`. -/
inductive Gate where
  | inp (i : ℕ)
  | cst (b : Bool)
  | neg (d : ℕ)
  | conj (d e : ℕ)
  | disj (d e : ℕ)
deriving DecidableEq, Repr

/-- A circuit is a list of gates. -/
abbrev Circuit := List Gate

/-- Value produced by a gate, given the input assignment and the list of
previously computed values, most recent first. -/
def Gate.val (g : Gate) (x : ℕ → Bool) (acc : List Bool) : Bool :=
  match g with
  | .inp i => x i
  | .cst b => b
  | .neg d => !(acc.getD d false)
  | .conj d e => (acc.getD d false) && (acc.getD e false)
  | .disj d e => (acc.getD d false) || (acc.getD e false)

/-- Run a circuit, accumulating computed values (most recent first). -/
def run (C : Circuit) (x : ℕ → Bool) (acc : List Bool) : List Bool :=
  C.foldl (fun acc g => g.val x acc :: acc) acc

/-- The output of a circuit is the value of its last gate. -/
def evalC (C : Circuit) (x : ℕ → Bool) : Bool := (run C x []).headD false

@[simp] lemma run_nil (x : ℕ → Bool) (acc : List Bool) : run [] x acc = acc := rfl

lemma run_cons (g : Gate) (C : Circuit) (x : ℕ → Bool) (acc : List Bool) :
    run (g :: C) x acc = run C x (g.val x acc :: acc) := rfl

lemma run_append (A B : Circuit) (x : ℕ → Bool) (acc : List Bool) :
    run (A ++ B) x acc = run B x (run A x acc) := by
  simp [run, List.foldl_append]

lemma run_singleton (g : Gate) (x : ℕ → Bool) (acc : List Bool) :
    run [g] x acc = g.val x acc :: acc := rfl

/-- `run C x acc` is `acc` with `C.length` new values pushed in front. -/
lemma run_eq_append (C : Circuit) (x : ℕ → Bool) (acc : List Bool) :
    ∃ T : List Bool, run C x acc = T ++ acc ∧ T.length = C.length := by
  induction C generalizing acc with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons g C ih =>
      obtain ⟨T, hT, hlen⟩ := ih (g.val x acc :: acc)
      refine ⟨T ++ [g.val x acc], ?_, ?_⟩
      · rw [run_cons, hT]; simp
      · simp [hlen]

lemma run_length (C : Circuit) (x : ℕ → Bool) (acc : List Bool) :
    (run C x acc).length = C.length + acc.length := by
  obtain ⟨T, hT, hlen⟩ := run_eq_append C x acc
  simp [hT, hlen]

/-- Reading past the freshly produced values reads the old accumulator. -/
lemma run_getD_add (C : Circuit) (x : ℕ → Bool) (acc : List Bool) (d : ℕ) :
    (run C x acc).getD (d + C.length) false = acc.getD d false := by
  obtain ⟨T, hT, hlen⟩ := run_eq_append C x acc
  rw [hT, List.getD_append_right]
  · simp [hlen]
  · omega

lemma getD_zero_eq_headD (l : List Bool) : l.getD 0 false = l.headD false := by
  cases l <;> rfl

/-! ### Boolean expressions and their compilation to circuits -/

/-- Boolean expression trees. -/
inductive BExpr where
  | var (i : ℕ)
  | cst (b : Bool)
  | neg (e : BExpr)
  | conj (a b : BExpr)
  | disj (a b : BExpr)
deriving Repr

/-- Value of an expression. -/
def BExpr.eval : BExpr → (ℕ → Bool) → Bool
  | .var i, x => x i
  | .cst b, _ => b
  | .neg e, x => !(e.eval x)
  | .conj a b, x => a.eval x && b.eval x
  | .disj a b, x => a.eval x || b.eval x

/-- Compile an expression into a straight-line circuit whose output is the
value of the expression. -/
def compile : BExpr → Circuit
  | .var i => [Gate.inp i]
  | .cst b => [Gate.cst b]
  | .neg e => compile e ++ [Gate.neg 0]
  | .conj a b => compile a ++ compile b ++ [Gate.conj (compile b).length 0]
  | .disj a b => compile a ++ compile b ++ [Gate.disj (compile b).length 0]

/-- Number of nodes of an expression. -/
def BExpr.size : BExpr → ℕ
  | .var _ => 1
  | .cst _ => 1
  | .neg e => e.size + 1
  | .conj a b => a.size + b.size + 1
  | .disj a b => a.size + b.size + 1

@[simp] lemma compile_length (e : BExpr) : (compile e).length = e.size := by
  induction e with
  | var i => rfl
  | cst b => rfl
  | neg e ih => simp [compile, BExpr.size, ih]
  | conj a b iha ihb => simp [compile, BExpr.size, iha, ihb]; ring
  | disj a b iha ihb => simp [compile, BExpr.size, iha, ihb]; ring

lemma run_compile_head (e : BExpr) (x : ℕ → Bool) (acc : List Bool) :
    (run (compile e) x acc).headD false = e.eval x := by
  induction e generalizing acc with
  | var i => rfl
  | cst b => rfl
  | neg e ih =>
      rw [compile, run_append, run_singleton]
      have h : (run (compile e) x acc).getD 0 false = e.eval x := by
        rw [getD_zero_eq_headD]; exact ih acc
      simp only [List.headD_cons, Gate.val, BExpr.eval, h]
  | conj a b iha ihb =>
      rw [compile, run_append, run_append, run_singleton]
      have hb2 : (run (compile b) x (run (compile a) x acc)).getD 0 false = b.eval x := by
        rw [getD_zero_eq_headD]; exact ihb _
      have ha2 : (run (compile b) x (run (compile a) x acc)).getD ((compile b).length) false
          = a.eval x := by
        have h1 := run_getD_add (compile b) x (run (compile a) x acc) 0
        rw [Nat.zero_add] at h1
        rw [h1, getD_zero_eq_headD]; exact iha acc
      simp only [List.headD_cons, Gate.val, BExpr.eval, ha2, hb2]
  | disj a b iha ihb =>
      rw [compile, run_append, run_append, run_singleton]
      have hb2 : (run (compile b) x (run (compile a) x acc)).getD 0 false = b.eval x := by
        rw [getD_zero_eq_headD]; exact ihb _
      have ha2 : (run (compile b) x (run (compile a) x acc)).getD ((compile b).length) false
          = a.eval x := by
        have h1 := run_getD_add (compile b) x (run (compile a) x acc) 0
        rw [Nat.zero_add] at h1
        rw [h1, getD_zero_eq_headD]; exact iha acc
      simp only [List.headD_cons, Gate.val, BExpr.eval, ha2, hb2]

@[simp] lemma evalC_compile (e : BExpr) (x : ℕ → Bool) : evalC (compile e) x = e.eval x :=
  run_compile_head e x []

end Frontier

import RequestProject.NP

/-!
# SAT is in NP

We build an explicit family of polynomial-size circuits which, given a bit
string `x` of length `2 v v` (encoding a CNF formula with `v` clauses over `v`
variables) and a witness assignment supplied on the inputs `|x|, …, |x| + v - 1`,
checks that the assignment satisfies the encoded formula.
-/

namespace Frontier

/-! ### Big conjunctions and disjunctions of expressions -/

/-- Conjunction of a list of expressions. -/
def bigAnd : List BExpr → BExpr
  | [] => .cst true
  | e :: l => .conj e (bigAnd l)

/-- Disjunction of a list of expressions. -/
def bigOr : List BExpr → BExpr
  | [] => .cst false
  | e :: l => .disj e (bigOr l)

@[simp] lemma bigAnd_eval (l : List BExpr) (x : ℕ → Bool) :
    (bigAnd l).eval x = l.all (fun e => e.eval x) := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [bigAnd, BExpr.eval, ih]

@[simp] lemma bigOr_eval (l : List BExpr) (x : ℕ → Bool) :
    (bigOr l).eval x = l.any (fun e => e.eval x) := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [bigOr, BExpr.eval, ih]

lemma bigAnd_size_le (l : List BExpr) (s : ℕ) (h : ∀ e ∈ l, e.size ≤ s) :
    (bigAnd l).size ≤ l.length * (s + 1) + 1 := by
  induction l with
  | nil => simp [bigAnd, BExpr.size]
  | cons e l ih =>
      have h1 : e.size ≤ s := h e (by simp)
      have h2 := ih (fun e' he' => h e' (by simp [he']))
      simp only [bigAnd, BExpr.size, List.length_cons]
      nlinarith

lemma bigOr_size_le (l : List BExpr) (s : ℕ) (h : ∀ e ∈ l, e.size ≤ s) :
    (bigOr l).size ≤ l.length * (s + 1) + 1 := by
  induction l with
  | nil => simp [bigOr, BExpr.size]
  | cons e l ih =>
      have h1 : e.size ≤ s := h e (by simp)
      have h2 := ih (fun e' he' => h e' (by simp [he']))
      simp only [bigOr, BExpr.size, List.length_cons]
      nlinarith

/-! ### The checking expression -/

/-- Does variable `i` satisfy clause `c`, according to the encoding bits? -/
def litExpr (n v c i : ℕ) : BExpr :=
  .disj (.conj (.var (2 * (c * v + i))) (.var (n + i)))
        (.conj (.var (2 * (c * v + i) + 1)) (.neg (.var (n + i))))

/-- Is clause `c` satisfied? -/
def clauseExpr (n v c : ℕ) : BExpr := bigOr ((List.range v).map (litExpr n v c))

/-- Is the whole encoded formula satisfied by the witness assignment? -/
def checkerExpr (n v : ℕ) : BExpr := bigAnd ((List.range v).map (clauseExpr n v))

lemma checkerExpr_eval (n v : ℕ) (b : ℕ → Bool) :
    (checkerExpr n v).eval b = true ↔
      ∀ c < v, ∃ i < v, (b (2 * (c * v + i)) = true ∧ b (n + i) = true) ∨
                        (b (2 * (c * v + i) + 1) = true ∧ b (n + i) = false) := by
  simp [checkerExpr, clauseExpr, litExpr, BExpr.eval, List.all_eq_true, List.any_eq_true,
    Bool.and_eq_true, Bool.or_eq_true]

lemma litExpr_size (n v c i : ℕ) : (litExpr n v c i).size = 8 := rfl

lemma clauseExpr_size_le (n v c : ℕ) : (clauseExpr n v c).size ≤ 9 * v + 1 := by
  have := bigOr_size_le ((List.range v).map (litExpr n v c)) 8 (by
    intro e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
    simp [litExpr_size])
  simpa [Nat.mul_comm] using this

lemma checkerExpr_size_le (n v : ℕ) : (checkerExpr n v).size ≤ v * (9 * v + 2) + 1 := by
  refine le_trans (bigAnd_size_le ((List.range v).map (clauseExpr n v)) (9 * v + 1) ?_) ?_
  · intro e he
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp he
    exact clauseExpr_size_le n v c
  · simp

/-! ### The verifier circuit family for SAT -/

/-- The verifier circuit for SAT on inputs of length `n`. -/
def satCirc (n : ℕ) : Circuit :=
  if n = 2 * sqv n * sqv n then compile (checkerExpr n (sqv n))
  else compile (BExpr.cst false)

lemma satCirc_length_le (n : ℕ) : (satCirc n).length ≤ 11 * (n + 1) ^ 1 := by
  rw [satCirc]
  split
  · rename_i hn
    rw [compile_length]
    have hn2 : n = 2 * (sqv n * sqv n) := by rw [mul_assoc] at hn; exact hn
    have hv : sqv n * sqv n ≤ n := by omega
    have hvn : sqv n ≤ n := by nlinarith [Nat.zero_le (sqv n)]
    have := checkerExpr_size_le n (sqv n)
    nlinarith
  · simp [compile, BExpr.size]
    omega

/-- **SAT is in NP.** -/
theorem satCirc_spec (x : List Bool) :
    SATLang x ↔ ∃ w : ℕ → Bool, evalC (satCirc x.length) (extend x w) = true := by
  classical
  set n := x.length with hn
  by_cases hcase : n = 2 * sqv n * sqv n
  · set v := sqv n with hv
    have hxlen : x.length = 2 * v * v := hcase
    -- the decoded formula
    have hdec : decodeCNF x = (List.range v).map (decClause x v) := by
      rw [decodeCNF, if_pos hcase]
    have hn2 : n = 2 * (v * v) := by rw [mul_assoc] at hcase; exact hcase
    have hbound : ∀ c i r, c < v → i < v → r < 2 → 2 * (c * v + i) + r < n := by
      intro c i r hc hi hr
      have h1 : c * v + i < v * v := by nlinarith
      omega
    -- reformulate the left-hand side
    have hL : SATLang x ↔ ∃ a : ℕ → Bool, ∀ c < v, ∃ i < v,
        (x.getD (2 * (c * v + i)) false = true ∧ a i = true) ∨
        (x.getD (2 * (c * v + i) + 1) false = true ∧ a i = false) := by
      rw [SATLang, Sat, hdec]
      refine exists_congr fun a => ?_
      simp only [satCNF, List.all_eq_true, List.mem_map, List.mem_range]
      constructor
      · intro h c hc
        exact (satClause_decClause a x v c).mp (h _ ⟨c, hc, rfl⟩)
      · rintro h c ⟨k, hk, rfl⟩
        exact (satClause_decClause a x v k).mpr (h k hk)
    -- reformulate the right-hand side
    have hR : (∃ w : ℕ → Bool, evalC (satCirc n) (extend x w) = true) ↔
        ∃ w : ℕ → Bool, ∀ c < v, ∃ i < v,
          (x.getD (2 * (c * v + i)) false = true ∧ w (n + i) = true) ∨
          (x.getD (2 * (c * v + i) + 1) false = true ∧ w (n + i) = false) := by
      refine exists_congr fun w => ?_
      rw [satCirc, if_pos hcase, evalC_compile, checkerExpr_eval]
      have he1 : ∀ c i r, c < v → i < v → r < 2 →
          extend x w (2 * (c * v + i) + r) = x.getD (2 * (c * v + i) + r) false := by
        intro c i r hc hi hr
        have := hbound c i r hc hi hr
        simp [extend, ← hn, this]
      have he2 : ∀ i, extend x w (n + i) = w (n + i) := by
        intro i; simp [extend, ← hn]
      constructor
      · intro h c hc
        obtain ⟨i, hi, hcase2⟩ := h c hc
        refine ⟨i, hi, ?_⟩
        rw [he2] at hcase2
        rcases hcase2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [show 2 * (c * v + i) = 2 * (c * v + i) + 0 from rfl, he1 c i 0 hc hi (by norm_num)]
            at h1
          exact Or.inl ⟨h1, h2⟩
        · rw [he1 c i 1 hc hi (by norm_num)] at h1
          exact Or.inr ⟨h1, h2⟩
      · intro h c hc
        obtain ⟨i, hi, hcase2⟩ := h c hc
        refine ⟨i, hi, ?_⟩
        rw [he2]
        rcases hcase2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine Or.inl ⟨?_, h2⟩
          rw [show 2 * (c * v + i) = 2 * (c * v + i) + 0 from rfl, he1 c i 0 hc hi (by norm_num)]
          exact h1
        · refine Or.inr ⟨?_, h2⟩
          rw [he1 c i 1 hc hi (by norm_num)]
          exact h1
    rw [hL, hR]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨fun k => a (k - n), fun c hc => by simpa using ha c hc⟩
    · rintro ⟨w, hw⟩
      exact ⟨fun i => w (n + i), fun c hc => hw c hc⟩
  · have hdec : decodeCNF x = [[]] := by
      rw [decodeCNF, if_neg (by rw [← hn]; exact hcase)]
    constructor
    · rintro ⟨a, ha⟩
      rw [hdec] at ha
      simp [satCNF, satClause] at ha
    · rintro ⟨w, hw⟩
      rw [satCirc, if_neg hcase] at hw
      simp [compile, evalC, run, Gate.val] at hw

/-- SAT, as a language of bit strings, belongs to NP. -/
def satVerifier : NPVerifier SATLang where
  circ := satCirc
  coeff := 11
  exponent := 1
  size_le := satCirc_length_le
  spec := satCirc_spec

end Frontier

import RequestProject.Tseitin

/-!
# Encoding CNF formulas as bit strings

To speak about SAT as a *language* (a set of bit strings) we fix a simple,
uniform encoding.  A bit string of length `2 * v * v` encodes a CNF formula with
`v` clauses over `v` variables: for each clause index `c < v` and each variable
index `i < v` there are two bits, saying whether the literal `xᵢ` (resp. `¬xᵢ`)
occurs in clause `c`.  Bit strings whose length is not of this shape decode to
the unsatisfiable formula `[[]]`.

Conversely `encode F` produces such a bit string; padding clauses are made
tautological, so `encode` preserves satisfiability.
-/

namespace Frontier

/-! ### A block-indexing lemma for `flatMap` over `List.range` -/

lemma flatMap_range_length {α : Type*} (L : ℕ) (f : ℕ → List α) (hf : ∀ c, (f c).length = L) :
    ∀ v : ℕ, ((List.range v).flatMap f).length = v * L := by
  intro v
  induction v with
  | zero => simp
  | succ v ih =>
      rw [List.range_succ, List.flatMap_append]
      simp [ih, hf, Nat.succ_mul]

lemma getD_flatMap_range {α : Type*} (L : ℕ) (f : ℕ → List α) (hf : ∀ c, (f c).length = L)
    (d : α) : ∀ {v c j : ℕ}, c < v → j < L →
      ((List.range v).flatMap f).getD (c * L + j) d = (f c).getD j d := by
  intro v
  induction v with
  | zero => intro c j hc; omega
  | succ v ih =>
      intro c j hc hj
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hlen : ((List.range v).flatMap f).length = v * L := flatMap_range_length L f hf v
      rcases Nat.lt_or_ge c v with hcv | hcv
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
        exact ih hcv hj
      · have hcv' : c = v := by omega
        subst hcv'
        rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
        congr 1
        omega

/-! ### Decoding -/

/-- The clause with index `c` decoded from the bit string `x`, for `v` variables. -/
def decClause (x : List Bool) (v c : ℕ) : Clause :=
  (List.range v).flatMap (fun i =>
    (if x.getD (2 * (c * v + i)) false then [(i, true)] else []) ++
    (if x.getD (2 * (c * v + i) + 1) false then [(i, false)] else []))

/-- The number of variables (and clauses) encoded by a bit string of length `n`. -/
def sqv (n : ℕ) : ℕ := Nat.sqrt (n / 2)

/-- The CNF formula encoded by a bit string. -/
def decodeCNF (x : List Bool) : CNF :=
  if x.length = 2 * sqv x.length * sqv x.length then
    (List.range (sqv x.length)).map (decClause x (sqv x.length))
  else [[]]

/-- The SAT language: bit strings encoding satisfiable CNF formulas. -/
def SATLang (x : List Bool) : Prop := Sat (decodeCNF x)

lemma satClause_decClause (a : ℕ → Bool) (x : List Bool) (v c : ℕ) :
    satClause a (decClause x v c) = true ↔
      ∃ i < v, (x.getD (2 * (c * v + i)) false = true ∧ a i = true) ∨
               (x.getD (2 * (c * v + i) + 1) false = true ∧ a i = false) := by
  have key : ∀ (p : Bool) (l : Lit),
      (if p then [l] else ([] : Clause)).any (satLit a) = (p && satLit a l) := by
    intro p l; cases p <;> simp
  simp only [decClause, satClause, List.any_flatMap, List.any_append, key,
    List.any_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true, satLit,
    beq_iff_eq]

/-! ### Encoding -/

private lemma le_foldr_max {l : List ℕ} {n : ℕ} (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons m l ih =>
      rcases List.mem_cons.mp h with h | h
      · subst h; simp
      · exact le_trans (ih h) (by simp)

/-- One more than the largest variable occurring in `F`. -/
def maxVarP1 (F : CNF) : ℕ := (F.flatMap (fun c => c.map (fun l => l.1 + 1))).foldr max 0

/-- The number of rows/columns used when encoding `F`. -/
def width (F : CNF) : ℕ := max F.length (maxVarP1 F)

lemma length_le_width (F : CNF) : F.length ≤ width F := le_max_left _ _

lemma lt_width_of_mem {F : CNF} {c : Clause} {l : Lit} (hc : c ∈ F) (hl : l ∈ c) :
    l.1 < width F := by
  have : l.1 + 1 ∈ F.flatMap (fun c => c.map (fun l => l.1 + 1)) := by
    rw [List.mem_flatMap]
    exact ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
  have hle := le_foldr_max this
  have h2 : maxVarP1 F ≤ width F := le_max_right _ _
  rw [maxVarP1] at h2
  omega

/-- The two bits recording the occurrences of variable `i` in clause `c` of `F`. -/
def encPair (F : CNF) (c i : ℕ) : List Bool :=
  if c < F.length then
    [decide ((i, true) ∈ F.getD c []), decide ((i, false) ∈ F.getD c [])]
  else [decide (i = 0), decide (i = 0)]

/-- The row of bits for clause `c`. -/
def encRow (F : CNF) (v c : ℕ) : List Bool := (List.range v).flatMap (encPair F c)

/-- The bit-string encoding of a CNF formula. -/
def encode (F : CNF) : List Bool := (List.range (width F)).flatMap (encRow F (width F))

private lemma encPair_length (F : CNF) (c i : ℕ) : (encPair F c i).length = 2 := by
  simp [encPair]; split <;> rfl

private lemma encRow_length (F : CNF) (v c : ℕ) : (encRow F v c).length = 2 * v := by
  rw [encRow, flatMap_range_length 2 _ (encPair_length F c) v]
  ring

lemma encode_length (F : CNF) : (encode F).length = 2 * width F * width F := by
  rw [encode, flatMap_range_length (2 * width F) _ (fun c => encRow_length F (width F) c)]
  ring

lemma encode_getD (F : CNF) {c i : ℕ} (hc : c < width F) (hi : i < width F) (r : ℕ) (hr : r < 2) :
    (encode F).getD (2 * (c * width F + i) + r) false = (encPair F c i).getD r false := by
  have h1 : 2 * (c * width F + i) + r = c * (2 * width F) + (i * 2 + r) := by ring
  rw [encode, h1,
    getD_flatMap_range (2 * width F) _ (fun c => encRow_length F (width F) c) false hc
      (by omega),
    encRow, getD_flatMap_range 2 _ (encPair_length F c) false hi (by omega)]

/-! ### The encoding preserves satisfiability -/

lemma decode_encode (F : CNF) :
    decodeCNF (encode F) = (List.range (width F)).map (decClause (encode F) (width F)) := by
  have hlen := encode_length F
  have hsq : (encode F).length / 2 = width F * width F := by
    rw [hlen]
    have : 2 * width F * width F = 2 * (width F * width F) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hs : sqv (encode F).length = width F := by
    rw [sqv, hsq, ← pow_two, Nat.sqrt_eq']
  rw [decodeCNF, hs, if_pos hlen]

lemma satCNF_decode_encode (F : CNF) (a : ℕ → Bool) :
    satCNF a (decodeCNF (encode F)) = true ↔ satCNF a F = true := by
  set v := width F with hv
  rw [decode_encode]
  simp only [satCNF, List.all_eq_true, List.mem_map, List.mem_range]
  constructor
  · rintro h c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have hkv : k < v := lt_of_lt_of_le hk (length_le_width F)
    have := h _ ⟨k, hkv, rfl⟩
    obtain ⟨i, hi, hcase⟩ := (satClause_decClause a (encode F) v k).mp this
    have hbits := encode_getD F hkv hi
    have hFk : F.getD k [] = F[k] := List.getD_eq_getElem F [] hk
    rcases hcase with ⟨hb, ha⟩ | ⟨hb, ha⟩
    · rw [show 2 * (k * v + i) = 2 * (k * v + i) + 0 from rfl, hbits 0 (by norm_num)] at hb
      simp only [encPair, if_pos hk, List.getD_cons_zero, decide_eq_true_eq, hFk] at hb
      exact List.any_eq_true.mpr ⟨(i, true), hb, by simp [satLit, ha]⟩
    · rw [hbits 1 (by norm_num)] at hb
      simp only [encPair, if_pos hk, List.getD_cons_succ, List.getD_cons_zero,
        decide_eq_true_eq, hFk] at hb
      exact List.any_eq_true.mpr ⟨(i, false), hb, by simp [satLit, ha]⟩
  · rintro h c ⟨k, hkv, rfl⟩
    rw [satClause_decClause]
    by_cases hk : k < F.length
    · have hFk : F.getD k [] = F[k] := List.getD_eq_getElem F [] hk
      have hsat := h F[k] (List.getElem_mem hk)
      obtain ⟨l, hl, hl2⟩ := List.any_eq_true.mp hsat
      have hiv : l.1 < v := lt_width_of_mem (List.getElem_mem hk) hl
      refine ⟨l.1, hiv, ?_⟩
      have hbits := encode_getD F hkv hiv
      have hl' : (l.1, l.2) ∈ F[k] := by simpa using hl
      cases hb : l.2 with
      | true =>
          left
          rw [hb] at hl'
          constructor
          · rw [show 2 * (k * v + l.1) = 2 * (k * v + l.1) + 0 from rfl, hbits 0 (by norm_num)]
            simp [encPair, hk, hl']
          · simpa [satLit, hb] using hl2
      | false =>
          right
          rw [hb] at hl'
          constructor
          · rw [hbits 1 (by norm_num)]
            simp [encPair, hk, hl']
          · simpa [satLit, hb] using hl2
    · have hv0 : 0 < v := by omega
      have hbits := encode_getD F hkv hv0
      refine ⟨0, hv0, ?_⟩
      cases ha : a 0 with
      | true =>
          left
          refine ⟨?_, rfl⟩
          rw [show 2 * (k * v + 0) = 2 * (k * v + 0) + 0 from rfl, hbits 0 (by norm_num)]
          simp [encPair, hk]
      | false =>
          right
          refine ⟨?_, rfl⟩
          rw [hbits 1 (by norm_num)]
          simp [encPair, hk]

/-- The bit-string encoding preserves satisfiability. -/
theorem satLang_encode (F : CNF) : SATLang (encode F) ↔ Sat F := by
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, (satCNF_decode_encode F a).mp ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, (satCNF_decode_encode F a).mpr ha⟩

end Frontier

import RequestProject.Checker

/-!
# The reduction: every NP language reduces to SAT

Combining the Tseitin transformation with the bit-string encoding of CNF
formulas gives, for every verifier circuit `C` and input `x`, a bit string
`reduce C x` which is in `SATLang` exactly when some witness makes `C` accept
`x`, and whose length is polynomial in the size of `C` and `|x|`.
-/

namespace Frontier

/-! ### Size bounds for the Tseitin formula -/

private lemma flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have h1 := h a (by simp)
      have h2 := ih (fun a' ha' => h a' (by simp [ha']))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith

private lemma foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ n ∈ l, n ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have h1 := h a (by simp)
      have h2 := ih (fun n hn => h n (by simp [hn]))
      simpa using ⟨h1, h2⟩

lemma maxVarP1_le (F : CNF) (B : ℕ) (h : ∀ c ∈ F, ∀ l ∈ c, l.1 + 1 ≤ B) : maxVarP1 F ≤ B := by
  refine foldr_max_le ?_
  intro n hn
  rw [List.mem_flatMap] at hn
  obtain ⟨c, hc, hn⟩ := hn
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
  exact h c hc l hl

lemma gateClauses_length_le (C : Circuit) (x : List Bool) (j : ℕ) :
    (gateClauses C x j).length ≤ 3 := by
  simp only [gateClauses]
  cases gateAt C j with
  | inp i => split <;> simp
  | cst b => simp
  | neg d => simp
  | conj d e => simp
  | disj d e => simp

lemma tseitin_length_le (C : Circuit) (x : List Bool) :
    (tseitin C x).length ≤ 3 * C.length + 2 := by
  have h := flatMap_length_le (List.range C.length) (fun j => gateClauses C x j) 3
    (fun j _ => gateClauses_length_le C x j)
  simp only [List.length_range] at h
  simp only [tseitin, List.length_append, List.length_cons, List.length_nil]
  omega

private lemma refv_le (j d : ℕ) : refv j d ≤ j := by
  simp only [refv, gv]
  split <;> omega

lemma gateClauses_var_le {C : Circuit} {x : List Bool} {j : ℕ} (hj : j < C.length) :
    ∀ c ∈ gateClauses C x j, ∀ l ∈ c, l.1 ≤ C.length := by
  have hgv : gv j ≤ C.length := by simp only [gv]; omega
  have hrefv : ∀ d, refv j d ≤ C.length := fun d => le_trans (refv_le j d) (le_of_lt hj)
  have hzero : (0 : ℕ) ≤ C.length := Nat.zero_le _
  simp only [gateClauses]
  cases hg : gateAt C j with
  | inp i =>
      have hmem : Gate.inp i ∈ C := by
        rw [← hg, show gateAt C j = C[j]'hj from List.getD_eq_getElem C (Gate.cst false) hj]
        exact List.getElem_mem hj
      have hfi : gv (firstInp C i) ≤ C.length := by
        have := List.idxOf_lt_length_of_mem hmem
        simp only [gv, firstInp]
        omega
      split <;>
        (intro c hc l hl
         fin_cases hc <;> fin_cases hl <;> first | exact hgv | exact hfi)
  | cst b =>
      intro c hc l hl
      fin_cases hc <;> fin_cases hl <;> exact hgv
  | neg d =>
      intro c hc l hl
      fin_cases hc <;> fin_cases hl <;> first | exact hgv | exact hrefv _
  | conj d e =>
      intro c hc l hl
      fin_cases hc <;> fin_cases hl <;> first | exact hgv | exact hrefv _
  | disj d e =>
      intro c hc l hl
      fin_cases hc <;> fin_cases hl <;> first | exact hgv | exact hrefv _

lemma tseitin_var_le (C : Circuit) (x : List Bool) :
    ∀ c ∈ tseitin C x, ∀ l ∈ c, l.1 ≤ C.length := by
  intro c hc l hl
  rw [tseitin] at hc
  simp only [List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatMap, List.mem_range] at hc
  rcases hc with (hc | ⟨j, hj, hc⟩) | hc
  · subst hc
    fin_cases hl
    exact Nat.zero_le _
  · exact gateClauses_var_le hj c hc l hl
  · subst hc
    fin_cases hl
    simp only [outLit]
    split
    · exact Nat.zero_le _
    · simp only [gv]; omega

lemma width_tseitin_le (C : Circuit) (x : List Bool) :
    width (tseitin C x) ≤ 3 * C.length + 2 := by
  refine max_le (tseitin_length_le C x) ?_
  refine maxVarP1_le _ _ ?_
  intro c hc l hl
  have := tseitin_var_le C x c hc l hl
  omega

/-! ### The reduction -/

/-- The reduction of "circuit `C` accepts `x` with some witness" to SAT. -/
def reduce (C : Circuit) (x : List Bool) : List Bool := encode (tseitin C x)

theorem reduce_correct (C : Circuit) (x : List Bool) :
    SATLang (reduce C x) ↔ ∃ w : ℕ → Bool, evalC C (extend x w) = true := by
  rw [reduce, satLang_encode, tseitin_correct]

theorem reduce_length_le (C : Circuit) (x : List Bool) :
    (reduce C x).length ≤ 2 * (3 * C.length + 2) * (3 * C.length + 2) := by
  rw [reduce, encode_length]
  have h := width_tseitin_le C x
  nlinarith [Nat.zero_le (width (tseitin C x))]

end Frontier

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

import RequestProject.Basic

/-!
# The Tseitin transformation

Given a circuit `C` and a partial input `x : List Bool` (the bits `x` fixing the
inputs `0, …, x.length - 1`), we build a CNF formula `tseitin C x` which is
satisfiable exactly when some completion of the input makes `C` output `true`.

The variables of `tseitin C x` are:

* variable `0`, a sentinel constrained to be `false` (used for out-of-range
  gate references);
* variable `j + 1` for each gate index `j`, holding the value of gate `j`.

In particular all variables are `≤ C.length`, which is what makes the size of
the produced formula polynomial in the size of the circuit.
-/

namespace Frontier

/-- The input assignment obtained by fixing the first `x.length` inputs to `x`
and using `w` for the remaining ones. -/
def extend (x : List Bool) (w : ℕ → Bool) : ℕ → Bool :=
  fun i => if i < x.length then x.getD i false else w i

/-! ### Prefix evaluation -/

/-- The list of values computed by the first `j` gates of `C` (most recent first). -/
def pre (C : Circuit) (x : ℕ → Bool) (j : ℕ) : List Bool := run (C.take j) x []

/-- The gate at position `j`, with a dummy default. -/
def gateAt (C : Circuit) (j : ℕ) : Gate := C.getD j (Gate.cst false)

lemma pre_length (C : Circuit) (x : ℕ → Bool) (j : ℕ) (h : j ≤ C.length) :
    (pre C x j).length = j := by
  simp [pre, run_length, h]

lemma pre_succ (C : Circuit) (x : ℕ → Bool) {j : ℕ} (h : j < C.length) :
    pre C x (j + 1) = ((gateAt C j).val x (pre C x j)) :: pre C x j := by
  have hj : C[j]?.toList = [C[j]'h] := by
    rw [List.getElem?_eq_getElem h]; rfl
  have htake : C.take (j + 1) = C.take j ++ [C[j]'h] := by
    rw [List.take_add_one, hj]
  have hgate : gateAt C j = C[j]'h := List.getD_eq_getElem C (Gate.cst false) h
  simp only [pre, htake, run_append, run_singleton, hgate]

lemma pre_full (C : Circuit) (x : ℕ → Bool) : pre C x C.length = run C x [] := by
  simp [pre]

lemma evalC_eq_pre (C : Circuit) (x : ℕ → Bool) :
    evalC C x = (pre C x C.length).headD false := by
  rw [pre_full]; rfl

lemma pre_getD_lt (C : Circuit) (x : ℕ → Bool) :
    ∀ {j d : ℕ}, d < j → j ≤ C.length →
      (pre C x j).getD d false = (pre C x (j - d)).headD false := by
  intro j
  induction j with
  | zero => intro d hd _; omega
  | succ j ih =>
      intro d hd hj
      have hs := pre_succ C x (show j < C.length by omega)
      cases d with
      | zero => simp [hs]
      | succ d =>
          rw [hs, List.getD_cons_succ, show j + 1 - (d + 1) = j - d from by omega]
          exact ih (by omega) (by omega)

lemma pre_getD_ge (C : Circuit) (x : ℕ → Bool) {j d : ℕ} (hd : j ≤ d) (hj : j ≤ C.length) :
    (pre C x j).getD d false = false :=
  List.getD_eq_default _ _ (by rw [pre_length C x j hj]; exact hd)

/-! ### The formula -/

/-- Variable holding the value of gate `j`. -/
def gv (j : ℕ) : ℕ := j + 1

lemma gv_ne_zero (j : ℕ) : gv j ≠ 0 := by simp [gv]

/-- The variable read by the reference `d` occurring in gate `j`: the variable of
gate `j - 1 - d`, or the `false` sentinel if the reference is out of range. -/
def refv (j d : ℕ) : ℕ := if d < j then gv (j - 1 - d) else 0

/-- Index of the first gate of `C` reading input `i`. -/
def firstInp (C : Circuit) (i : ℕ) : ℕ := C.idxOf (Gate.inp i)

/-- Clauses defining the value of gate `j` of `C`, with the first `x.length`
inputs fixed to the bits of `x`. -/
def gateClauses (C : Circuit) (x : List Bool) (j : ℕ) : CNF :=
  match gateAt C j with
  | .inp i =>
      if i < x.length then [[(gv j, x.getD i false)]]
      else [[(gv j, false), (gv (firstInp C i), true)],
            [(gv j, true), (gv (firstInp C i), false)]]
  | .cst b => [[(gv j, b)]]
  | .neg d => [[(gv j, true), (refv j d, true)], [(gv j, false), (refv j d, false)]]
  | .conj d e =>
      [[(gv j, false), (refv j d, true)], [(gv j, false), (refv j e, true)],
       [(gv j, true), (refv j d, false), (refv j e, false)]]
  | .disj d e =>
      [[(gv j, true), (refv j d, false)], [(gv j, true), (refv j e, false)],
       [(gv j, false), (refv j d, true), (refv j e, true)]]

/-- The literal asserting that the circuit outputs `true` (using the sentinel for
the degenerate empty circuit, which outputs `false`). -/
def outLit (C : Circuit) : Lit :=
  if C.length = 0 then (0, true) else (gv (C.length - 1), true)

/-- The Tseitin encoding of "`C` outputs `true` on some input extending `x`". -/
def tseitin (C : Circuit) (x : List Bool) : CNF :=
  [[(0, false)]] ++ (List.range C.length).flatMap (fun j => gateClauses C x j) ++ [[outLit C]]

/-! ### Extraction of the individual constraints -/

lemma sat_tseitin_sentinel {C : Circuit} {x : List Bool} {a : ℕ → Bool}
    (h : satCNF a (tseitin C x) = true) : a 0 = false := by
  simp [tseitin, satCNF, satClause, satLit] at h
  tauto

lemma sat_tseitin_gate {C : Circuit} {x : List Bool} {a : ℕ → Bool}
    (h : satCNF a (tseitin C x) = true) {j : ℕ} (hj : j < C.length) :
    satCNF a (gateClauses C x j) = true := by
  simp only [tseitin, satCNF_append, Bool.and_eq_true] at h
  obtain ⟨⟨-, h2⟩, -⟩ := h
  simp only [satCNF, List.all_flatMap, List.all_eq_true, List.mem_range] at h2 ⊢
  exact fun c hc => h2 j hj c hc

lemma sat_tseitin_out {C : Circuit} {x : List Bool} {a : ℕ → Bool}
    (h : satCNF a (tseitin C x) = true) : satLit a (outLit C) = true := by
  simp only [tseitin, satCNF_append, Bool.and_eq_true] at h
  obtain ⟨-, h3⟩ := h
  simpa [satCNF, satClause] using h3

lemma satCNF_tseitin_of {C : Circuit} {x : List Bool} {a : ℕ → Bool}
    (h0 : a 0 = false)
    (hg : ∀ j, j < C.length → satCNF a (gateClauses C x j) = true)
    (hout : satLit a (outLit C) = true) :
    satCNF a (tseitin C x) = true := by
  simp only [tseitin, satCNF_append, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [satCNF, satClause, satLit, h0]
  · simp only [satCNF, List.all_flatMap, List.all_eq_true, List.mem_range]
    intro j hj c hc
    have := hg j hj
    simp only [satCNF, List.all_eq_true] at this
    exact this c hc
  · simpa [satCNF, satClause] using hout

/-! ### Boolean helper lemmas -/

private lemma bool_iff_of (Y U : Bool) (h1 : Y = true ∨ U = true) (h2 : Y = false ∨ U = false) :
    Y = !U := by revert h1 h2; cases Y <;> cases U <;> simp

private lemma bool_eq_of (Y U : Bool) (h1 : Y = false ∨ U = true) (h2 : Y = true ∨ U = false) :
    Y = U := by revert h1 h2; cases Y <;> cases U <;> simp

private lemma bool_and_of (Y U W : Bool) (h1 : Y = false ∨ U = true) (h2 : Y = false ∨ W = true)
    (h3 : Y = true ∨ U = false ∨ W = false) : Y = (U && W) := by
  revert h1 h2 h3; cases Y <;> cases U <;> cases W <;> simp

private lemma bool_or_of (Y U W : Bool) (h1 : Y = true ∨ U = false) (h2 : Y = true ∨ W = false)
    (h3 : Y = false ∨ U = true ∨ W = true) : Y = (U || W) := by
  revert h1 h2 h3; cases Y <;> cases U <;> cases W <;> simp

/-! ### Correctness of the encoding -/

lemma refv_eq (C : Circuit) (ext a : ℕ → Bool) (h0 : a 0 = false) {j : ℕ} (hj : j ≤ C.length)
    (ih : ∀ k, k < j → a (gv k) = (pre C ext (k + 1)).headD false) (d : ℕ) :
    a (refv j d) = (pre C ext j).getD d false := by
  by_cases hd : d < j
  · rw [refv, if_pos hd, ih (j - 1 - d) (by omega), pre_getD_lt C ext hd hj]
    congr 2
    omega
  · rw [refv, if_neg hd, h0, pre_getD_ge C ext (by omega) hj]

lemma gateClauses_iff {C : Circuit} {x : List Bool} {ext a : ℕ → Bool} {j : ℕ}
    (hj : j < C.length)
    (hrefj : ∀ d, a (refv j d) = (pre C ext j).getD d false)
    (hx : ∀ i, i < x.length → ext i = x.getD i false)
    (hinp : ∀ i, x.length ≤ i → Gate.inp i ∈ C → ext i = a (gv (firstInp C i))) :
    satCNF a (gateClauses C x j) = true ↔ a (gv j) = (gateAt C j).val ext (pre C ext j) := by
  have hmem : gateAt C j ∈ C := by
    rw [show gateAt C j = C[j]'hj from List.getD_eq_getElem C (Gate.cst false) hj]
    exact List.getElem_mem hj
  cases hg : gateAt C j with
  | inp i =>
      rw [hg] at hmem
      by_cases hi : i < x.length
      · simp only [gateClauses, hg, hi, if_pos, satCNF, satClause, satLit, Gate.val,
          List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.or_false,
          Bool.and_true, beq_iff_eq]
        rw [hx i hi]
      · simp only [gateClauses, hg, hi, if_neg, not_false_iff, satCNF, satClause, satLit,
          Gate.val, List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.or_false,
          Bool.and_true, beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true]
        rw [hinp i (by omega) hmem]
        constructor
        · rintro ⟨h1, h2⟩
          exact bool_eq_of _ _ h1 h2
        · intro h; rw [h]
          cases a (gv (firstInp C i)) <;> simp
  | cst b =>
      simp only [gateClauses, hg, satCNF, satClause, satLit, Gate.val, List.all_cons,
        List.all_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq]
  | neg d =>
      simp only [gateClauses, hg, satCNF, satClause, satLit, Gate.val, List.all_cons,
        List.all_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq,
        Bool.and_eq_true, Bool.or_eq_true]
      rw [← hrefj d]
      constructor
      · rintro ⟨h1, h2⟩; exact bool_iff_of _ _ h1 h2
      · intro h; rw [h]; cases a (refv j d) <;> simp
  | conj d e =>
      simp only [gateClauses, hg, satCNF, satClause, satLit, Gate.val, List.all_cons,
        List.all_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq,
        Bool.and_eq_true, Bool.or_eq_true]
      rw [← hrefj d, ← hrefj e]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact bool_and_of _ _ _ h1 h2 h3
      · intro h; rw [h]; cases a (refv j d) <;> cases a (refv j e) <;> simp
  | disj d e =>
      simp only [gateClauses, hg, satCNF, satClause, satLit, Gate.val, List.all_cons,
        List.all_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq,
        Bool.and_eq_true, Bool.or_eq_true]
      rw [← hrefj d, ← hrefj e]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact bool_or_of _ _ _ h1 h2 h3
      · intro h; rw [h]; cases a (refv j d) <;> cases a (refv j e) <;> simp

/-- If some completion of the input makes the circuit output `true`, the Tseitin
formula is satisfiable. -/
theorem sat_tseitin_of_eval {C : Circuit} {x : List Bool} {w : ℕ → Bool}
    (h : evalC C (extend x w) = true) : Sat (tseitin C x) := by
  classical
  set ext := extend x w with hext
  refine ⟨fun v => if v = 0 then false else (pre C ext v).headD false, ?_⟩
  set a : ℕ → Bool := fun v => if v = 0 then false else (pre C ext v).headD false with ha
  have h0 : a 0 = false := by simp [ha]
  have hval : ∀ j, a (gv j) = (pre C ext (j + 1)).headD false := by
    intro j; simp [ha, gv]
  have hnonempty : 0 < C.length := by
    by_contra hc
    have : C = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [this] at h
    simp [evalC] at h
  have hx : ∀ i, i < x.length → ext i = x.getD i false := by
    intro i hi; simp [hext, extend, hi]
  have hinp : ∀ i, x.length ≤ i → Gate.inp i ∈ C → ext i = a (gv (firstInp C i)) := by
    intro i hi hmem
    have hlt : firstInp C i < C.length := List.idxOf_lt_length_of_mem hmem
    have hgi : gateAt C (firstInp C i) = Gate.inp i := by
      rw [show gateAt C (firstInp C i) = C[firstInp C i]'hlt from
        List.getD_eq_getElem C (Gate.cst false) hlt]
      exact List.getElem_idxOf hlt
    rw [hval, pre_succ C ext hlt, List.headD_cons, hgi]
    rfl
  refine satCNF_tseitin_of h0 (fun j hj => ?_) ?_
  · rw [gateClauses_iff hj (refv_eq C ext a h0 (le_of_lt hj) (fun k _ => hval k)) hx hinp,
      hval j, pre_succ C ext hj, List.headD_cons]
  · have : outLit C = (gv (C.length - 1), true) := by
      rw [outLit, if_neg (by omega)]
    rw [this, satLit, hval]
    have : C.length - 1 + 1 = C.length := by omega
    rw [this]
    rw [← evalC_eq_pre, h]
    rfl

/-- If the Tseitin formula is satisfiable, some completion of the input makes the
circuit output `true`. -/
theorem eval_of_sat_tseitin {C : Circuit} {x : List Bool} (h : Sat (tseitin C x)) :
    ∃ w : ℕ → Bool, evalC C (extend x w) = true := by
  classical
  obtain ⟨a, ha⟩ := h
  set w : ℕ → Bool := fun i => a (gv (firstInp C i)) with hw
  refine ⟨w, ?_⟩
  set ext := extend x w with hext
  have h0 : a 0 = false := sat_tseitin_sentinel ha
  have hx : ∀ i, i < x.length → ext i = x.getD i false := by
    intro i hi; simp [hext, extend, hi]
  have hinp : ∀ i, x.length ≤ i → Gate.inp i ∈ C → ext i = a (gv (firstInp C i)) := by
    intro i hi _
    simp [hext, extend, hw, Nat.not_lt.mpr hi]
  have hval : ∀ j, j < C.length → a (gv j) = (pre C ext (j + 1)).headD false := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hrefj := refv_eq C ext a h0 (le_of_lt hj)
        (fun k hk => ih k hk (by omega))
      have := (gateClauses_iff hj hrefj hx hinp).mp (sat_tseitin_gate ha hj)
      rw [this, pre_succ C ext hj, List.headD_cons]
  have hnonempty : 0 < C.length := by
    by_contra hc
    have hlen : C.length = 0 := by omega
    have hout := sat_tseitin_out ha
    rw [outLit, if_pos hlen] at hout
    simp [satLit, h0] at hout
  have hout := sat_tseitin_out ha
  rw [outLit, if_neg (by omega), satLit] at hout
  have h1 : a (gv (C.length - 1)) = true := by simpa using hout
  rw [hval _ (by omega), show C.length - 1 + 1 = C.length from by omega] at h1
  rw [evalC_eq_pre]
  exact h1

/-- **Correctness of the Tseitin transformation.** -/
theorem tseitin_correct (C : Circuit) (x : List Bool) :
    Sat (tseitin C x) ↔ ∃ w : ℕ → Bool, evalC C (extend x w) = true :=
  ⟨eval_of_sat_tseitin, fun ⟨_, hw⟩ => sat_tseitin_of_eval hw⟩

end Frontier

