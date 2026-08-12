import RequestProject.Tseitin

/-!
# The Cook–Levin theorem: SAT is NP-complete

We work with languages of bit strings, `L : List Bool → Prop`.

Membership in NP is expressed by a *verifier*: a family of Boolean circuits
(straight-line programs) `V.ckt n`, of size polynomial in `n`, which takes an input
`x` of length `n` together with a witness `w` of polynomially bounded length
`V.wit n`, and accepts or rejects.  A string `x` is in the language iff some witness
is accepted.

* **SAT ∈ NP** (`sat_mem_NP`): a formula `F` is satisfiable iff there is a witness
  bit string `w` of length `numVars F` such that the (explicitly cost-instrumented)
  evaluator accepts, and that evaluation costs at most `2 * cnfSize F + 1` steps,
  i.e. linear time.

* **SAT is NP-hard** (`cook_levin_hardness`): for every verifier `V` and input `x`,
  the explicitly constructed formula `cookReduction V x` — obtained by the Tseitin
  transformation of the verifier circuit with the bits of `x` hard-wired — is
  satisfiable iff `x` belongs to the language of `V`; and its size is polynomially
  bounded in `|x|`, the construction being computable in linear time in the size of
  the circuit.

Both halves are combined in `cook_levin`.
-/

namespace Frontier

/-- The assignment described by a list of bits (missing bits default to `false`). -/
def assignOf (w : List Bool) : ℕ → Bool := fun i => w.getD i false

/-! ## SAT is in NP -/

/-- **SAT ∈ NP.**  A CNF formula is satisfiable iff it has a satisfying assignment
given by a bit string of length `numVars F`. -/
theorem sat_iff_exists_witness (F : CNF) :
    SAT F ↔ ∃ w : List Bool, w.length = numVars F ∧ evalCNF (assignOf w) F = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(List.range (numVars F)).map σ, by simp, ?_⟩
    rw [evalCNF_congr (σ := σ) (τ := assignOf ((List.range (numVars F)).map σ)) ?_] at hσ
    · exact hσ
    · intro i hi
      simp [assignOf, List.getD_eq_getElem?_getD, hi]
  · rintro ⟨w, -, hw⟩
    exact ⟨assignOf w, hw⟩

/-- Verifying a candidate satisfying assignment takes linear time. -/
theorem sat_verification_cost (F : CNF) (w : List Bool) :
    (evalCNFCost (assignOf w) F).1 = evalCNF (assignOf w) F ∧
      (evalCNFCost (assignOf w) F).2 ≤ 2 * cnfSize F + 1 :=
  ⟨evalCNFCost_fst _ _, evalCNFCost_snd_le _ _⟩

/-! ## NP via circuit verifiers -/

/-- A polynomial-time verifier, presented as a polynomial-size family of Boolean
circuits: `ckt n` is the circuit used on inputs of length `n`, it reads the `n` input
bits and `wit n` witness bits, and its last wire carries the answer. -/
structure Verifier where
  /-- Length of the witness for inputs of length `n`. -/
  wit : ℕ → ℕ
  /-- The verifier circuit for inputs of length `n`. -/
  ckt : ℕ → SLP
  /-- Each circuit is a well-formed straight-line program. -/
  wf : ∀ n, WF (ckt n)
  /-- Each circuit has at least one gate (its output). -/
  ne : ∀ n, ckt n ≠ []
  /-- The circuit reads only the input bits and the witness bits. -/
  reads : ∀ n, InputsLT (n + wit n) (ckt n)
  /-- The circuits have polynomial size. -/
  polyC : ∃ c k : ℕ, ∀ n, (ckt n).length ≤ c * (n + 1) ^ k
  /-- The witnesses have polynomially bounded length. -/
  polyW : ∃ c k : ℕ, ∀ n, wit n ≤ c * (n + 1) ^ k

namespace Verifier

variable (V : Verifier)

/-- The verifier accepts input `x` with witness `w`. -/
def accepts (x w : List Bool) : Prop :=
  wireVal (assignOf (x ++ w)) (V.ckt x.length) ((V.ckt x.length).length - 1) = true

/-- The language recognized by the verifier. -/
def lang (x : List Bool) : Prop :=
  ∃ w : List Bool, w.length = V.wit x.length ∧ V.accepts x w

end Verifier

/-- A language is in NP if it is recognized by some polynomial-size circuit verifier. -/
def InNP (L : List Bool → Prop) : Prop := ∃ V : Verifier, ∀ x, L x ↔ V.lang x

/-! ## SAT is NP-hard -/

/-- The Cook–Levin reduction: the Tseitin encoding of the verifier circuit for length
`|x|`, with the bits of `x` hard-wired into the first input variables. -/
def cookReduction (V : Verifier) (x : List Bool) : CNF :=
  reduceSLP (V.ckt x.length) x

lemma assignOf_append_left {x w : List Bool} {i : ℕ} (hi : i < x.length) :
    assignOf (x ++ w) i = assignOf x i := by
  simp [assignOf, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma assignOf_append_right {x w : List Bool} {i : ℕ} (hi : x.length ≤ i) :
    assignOf (x ++ w) i = assignOf w (i - x.length) := by
  simp [assignOf, List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

/-- **NP-hardness of SAT.**  For every verifier `V` and every input `x`, the formula
`cookReduction V x` is satisfiable exactly when `x` is in the language of `V`. -/
theorem sat_cookReduction_iff (V : Verifier) (x : List Bool) :
    SAT (cookReduction V x) ↔ V.lang x := by
  set n := x.length with hn
  set gs := V.ckt n with hgs
  rw [cookReduction, ← hn, ← hgs,
    sat_reduceSLP_iff (V.wf n) (V.ne n) x]
  constructor
  · rintro ⟨y, hy, hout⟩
    -- read off the witness from the free assignment `y`
    refine ⟨(List.range (V.wit n)).map (fun k => y (n + k)), by simp [hn], ?_⟩
    have hagree : ∀ i, i < n + V.wit n →
        assignOf (x ++ (List.range (V.wit n)).map (fun k => y (n + k))) i = y i := by
      intro i hi
      rcases lt_or_ge i n with h | h
      · rw [assignOf_append_left (by omega)]
        rw [hy i (by omega)]
        simp [assignOf]
      · rw [assignOf_append_right (by omega)]
        have hlt : i - n < V.wit n := by omega
        simp only [assignOf, List.getD_eq_getElem?_getD]
        rw [List.getElem?_map, List.getElem?_range hlt]
        simp only [Option.map_some, Option.getD_some]
        congr 1
        omega
    unfold Verifier.accepts
    rw [← hn, ← hgs]
    rw [wireVal_congr (n := n + V.wit n) (V.reads n) hagree]
    exact hout
  · rintro ⟨w, hw, hacc⟩
    refine ⟨assignOf (x ++ w), ?_, ?_⟩
    · intro i hi
      rw [assignOf_append_left hi]
      simp [assignOf]
    · unfold Verifier.accepts at hacc
      rw [← hn, ← hgs] at hacc
      exact hacc

/-- The cost-instrumented Cook–Levin reduction: it returns the formula together with
the exact number of elementary steps used to build it. -/
def cookReductionRun (V : Verifier) (x : List Bool) : CNF × ℕ :=
  reduceBuild (V.ckt x.length) x

@[simp] theorem cookReductionRun_fst (V : Verifier) (x : List Bool) :
    (cookReductionRun V x).1 = cookReduction V x := by
  simp [cookReductionRun, cookReduction]

/-- The reduction has polynomially bounded output size **and** is computed in
polynomially many elementary steps: it is a genuine polynomial-time many-one
reduction. -/
theorem cookReduction_poly (V : Verifier) :
    ∃ c k : ℕ, ∀ x : List Bool,
      cnfSize (cookReduction V x) ≤ c * (x.length + 1) ^ k ∧
        (cookReductionRun V x).2 ≤ c * (x.length + 1) ^ k := by
  obtain ⟨c, k, hc⟩ := V.polyC
  refine ⟨11 * c + 5, k + 1, ?_⟩
  intro x
  set n := x.length with hn
  have h1 : cnfSize (cookReduction V x) ≤ 10 * (V.ckt n).length + 2 * n + 2 :=
    cnfSize_reduceSLP _ _
  have h1' : (cookReductionRun V x).2 = 11 * (V.ckt n).length + 2 * n + 3 :=
    reduceBuild_snd _ _
  have h2 : (V.ckt n).length ≤ c * (n + 1) ^ k := hc n
  have h3 : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : n + 1 ≤ (n + 1) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have h5 : c * (n + 1) ^ k ≤ c * (n + 1) ^ (k + 1) := Nat.mul_le_mul_left _ h3
  have key : 11 * (V.ckt n).length + 2 * n + 3
      ≤ (11 * c + 5) * (n + 1) ^ (k + 1) := by
    calc 11 * (V.ckt n).length + 2 * n + 3
        ≤ 11 * (c * (n + 1) ^ k) + 5 * (n + 1) := by omega
      _ ≤ 11 * (c * (n + 1) ^ (k + 1)) + 5 * (n + 1) ^ (k + 1) := by omega
      _ ≤ (11 * c + 5) * (n + 1) ^ (k + 1) := by ring_nf; omega
  exact ⟨by omega, by omega⟩

/-- **NP-hardness of SAT**, stated for an arbitrary language in NP: every such
language many-one reduces to SAT via the explicit reduction `cookReduction`, which
produces a formula of polynomial size in polynomially many steps. -/
theorem cook_levin_hardness {L : List Bool → Prop} (hL : InNP L) :
    ∃ f : List Bool → CNF × ℕ, (∀ x, L x ↔ SAT (f x).1) ∧
      ∃ c k : ℕ, ∀ x, cnfSize (f x).1 ≤ c * (x.length + 1) ^ k ∧
        (f x).2 ≤ c * (x.length + 1) ^ k := by
  obtain ⟨V, hV⟩ := hL
  refine ⟨cookReductionRun V, fun x => ?_, ?_⟩
  · rw [cookReductionRun_fst]
    exact (hV x).trans (sat_cookReduction_iff V x).symm
  · obtain ⟨c, k, hck⟩ := cookReduction_poly V
    exact ⟨c, k, fun x => ⟨by rw [cookReductionRun_fst]; exact (hck x).1, (hck x).2⟩⟩

/-! ## The Cook–Levin theorem -/

/-- **The Cook–Levin theorem: SAT is NP-complete.**

1. *SAT is in NP*: a formula `F` is satisfiable iff there is a witness bit string of
   length `numVars F` accepted by the checker, and the checker runs in linear time
   (`2 * cnfSize F + 1` elementary steps at most).
2. *SAT is NP-hard*: for every language `L` recognized by a polynomial-size circuit
   verifier there is a many-one reduction of `L` to SAT which, on input `x`, outputs
   a formula of size polynomial in `|x|` using polynomially many elementary steps;
   the reduction is the explicit Tseitin-style construction `cookReductionRun`. -/
theorem cook_levin :
    (∀ F : CNF, SAT F ↔ ∃ w : List Bool, w.length = numVars F ∧
        (evalCNFCost (assignOf w) F).1 = true) ∧
    (∀ (F : CNF) (w : List Bool), (evalCNFCost (assignOf w) F).2 ≤ 2 * cnfSize F + 1) ∧
    (∀ L : List Bool → Prop, InNP L → ∃ f : List Bool → CNF × ℕ,
        (∀ x, L x ↔ SAT (f x).1) ∧
        ∃ c k : ℕ, ∀ x, cnfSize (f x).1 ≤ c * (x.length + 1) ^ k ∧
          (f x).2 ≤ c * (x.length + 1) ^ k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F
    rw [sat_iff_exists_witness F]
    constructor
    · rintro ⟨w, hlen, hw⟩
      exact ⟨w, hlen, by rw [evalCNFCost_fst]; exact hw⟩
    · rintro ⟨w, hlen, hw⟩
      exact ⟨w, hlen, by rwa [evalCNFCost_fst] at hw⟩
  · intro F w
    exact evalCNFCost_snd_le _ _
  · intro L hL
    exact cook_levin_hardness hL

end Frontier

import Mathlib

/-!
# Propositional formulas in conjunctive normal form (CNF) and the SAT problem

This file sets up the basic syntax and semantics of CNF formulas over the variable
set `ℕ`, defines the satisfiability predicate `Frontier.SAT`, an explicitly
cost-instrumented evaluator (used to witness that verifying a satisfying assignment
takes linear time in the size of the formula), and basic congruence/size lemmas.
-/

namespace Frontier

/-- A literal: a variable together with a polarity (`neg = true` means negated). -/
structure Lit where
  var : ℕ
  neg : Bool
deriving DecidableEq, Repr

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF := List Clause

/-- Value of a literal under an assignment. -/
def evalLit (σ : ℕ → Bool) (l : Lit) : Bool := xor l.neg (σ l.var)

/-- Value of a clause under an assignment (disjunction). -/
def evalClause (σ : ℕ → Bool) (C : Clause) : Bool := C.any (evalLit σ)

/-- Value of a CNF formula under an assignment (conjunction). -/
def evalCNF (σ : ℕ → Bool) (F : CNF) : Bool := F.all (evalClause σ)

/-- The satisfiability predicate: the SAT problem. -/
def SAT (F : CNF) : Prop := ∃ σ : ℕ → Bool, evalCNF σ F = true

@[simp] lemma evalCNF_nil (σ : ℕ → Bool) : evalCNF σ [] = true := rfl

@[simp] lemma evalCNF_cons (σ : ℕ → Bool) (C : Clause) (F : CNF) :
    evalCNF σ (C :: F) = (evalClause σ C && evalCNF σ F) := rfl

lemma evalCNF_append (σ : ℕ → Bool) (F G : CNF) :
    evalCNF σ (F ++ G) = (evalCNF σ F && evalCNF σ G) := by
  simp [evalCNF]

lemma evalCNF_eq_true_iff (σ : ℕ → Bool) (F : CNF) :
    evalCNF σ F = true ↔ ∀ C ∈ F, evalClause σ C = true := by
  simp [evalCNF]

lemma evalClause_eq_true_iff (σ : ℕ → Bool) (C : Clause) :
    evalClause σ C = true ↔ ∃ l ∈ C, evalLit σ l = true := by
  simp [evalClause]

/-! ### Size measures -/

/-- The number of clauses plus the total number of literal occurrences. -/
def cnfSize (F : CNF) : ℕ := F.length + (F.map List.length).sum

lemma cnfSize_append (F G : CNF) : cnfSize (F ++ G) = cnfSize F + cnfSize G := by
  simp [cnfSize]; omega

/-! ### A cost-instrumented evaluator

`evalCNFCost` returns the truth value of the formula together with the exact number
of elementary steps used; the value agrees with `evalCNF` and the cost is linear in
the size of the formula.  This witnesses that checking a candidate satisfying
assignment is a polynomial-time (indeed linear-time) computation. -/

/-- Cost-instrumented clause evaluation. -/
def evalClauseCost (σ : ℕ → Bool) : Clause → Bool × ℕ
  | [] => (false, 1)
  | l :: C => let r := evalClauseCost σ C; (evalLit σ l || r.1, r.2 + 1)

/-- Cost-instrumented CNF evaluation. -/
def evalCNFCost (σ : ℕ → Bool) : CNF → Bool × ℕ
  | [] => (true, 1)
  | C :: F =>
      let r1 := evalClauseCost σ C
      let r2 := evalCNFCost σ F
      (r1.1 && r2.1, r1.2 + r2.2 + 1)

lemma evalClauseCost_fst (σ : ℕ → Bool) (C : Clause) :
    (evalClauseCost σ C).1 = evalClause σ C := by
  induction C with
  | nil => rfl
  | cons l C ih => simp [evalClauseCost, evalClause, ih, evalClause] at *

lemma evalClauseCost_snd (σ : ℕ → Bool) (C : Clause) :
    (evalClauseCost σ C).2 = C.length + 1 := by
  induction C with
  | nil => rfl
  | cons l C ih => simp [evalClauseCost, ih]

lemma evalCNFCost_fst (σ : ℕ → Bool) (F : CNF) :
    (evalCNFCost σ F).1 = evalCNF σ F := by
  induction F with
  | nil => rfl
  | cons C F ih => simp [evalCNFCost, evalClauseCost_fst, ih]

/-- Checking an assignment costs at most `2 * cnfSize F + 1` elementary steps. -/
lemma evalCNFCost_snd_le (σ : ℕ → Bool) (F : CNF) :
    (evalCNFCost σ F).2 ≤ 2 * cnfSize F + 1 := by
  induction F with
  | nil => simp [evalCNFCost, cnfSize]
  | cons C F ih =>
      simp only [evalCNFCost, evalClauseCost_snd, cnfSize] at *
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-! ### Variables -/

/-- A bound on all variables occurring in `F`: every variable of `F` is `< numVars F`. -/
def numVars (F : CNF) : ℕ := ((F.flatten).map (fun l => l.var + 1)).foldr max 0

lemma lt_numVars {F : CNF} {C : Clause} {l : Lit} (hC : C ∈ F) (hl : l ∈ C) :
    l.var < numVars F := by
  have hmem : l ∈ F.flatten := List.mem_flatten.2 ⟨C, hC, hl⟩
  have : ∀ (L : List Lit), l ∈ L → l.var + 1 ≤ (L.map (fun l => l.var + 1)).foldr max 0 := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
        intro h
        rcases List.mem_cons.1 h with h | h
        · subst h; simp
        · exact le_trans (ih h) (by simp)
  exact this _ hmem

/-- The value of a clause only depends on the values of the variables occurring in it. -/
lemma evalClause_congr {σ τ : ℕ → Bool} {C : Clause}
    (h : ∀ l ∈ C, σ l.var = τ l.var) : evalClause σ C = evalClause τ C := by
  simp only [evalClause]
  induction C with
  | nil => rfl
  | cons a C ih =>
      simp only [List.any_cons]
      rw [ih (fun l hl => h l (List.mem_cons_of_mem _ hl))]
      have : evalLit σ a = evalLit τ a := by
        simp [evalLit, h a (List.mem_cons_self ..)]
      rw [this]

/-- The truth value of a CNF formula only depends on the values of its variables. -/
lemma evalCNF_congr {σ τ : ℕ → Bool} {F : CNF}
    (h : ∀ i < numVars F, σ i = τ i) : evalCNF σ F = evalCNF τ F := by
  have hcl : ∀ C ∈ F, evalClause σ C = evalClause τ C := by
    intro C hC
    exact evalClause_congr (fun l hl => h l.var (lt_numVars hC hl))
  clear h
  simp only [evalCNF]
  induction F with
  | nil => rfl
  | cons C F ih =>
      simp only [List.all_cons]
      rw [hcl C (List.mem_cons_self ..),
        ih (fun C' hC' => hcl C' (List.mem_cons_of_mem _ hC'))]

end Frontier

import RequestProject.CNF

/-!
# Boolean straight-line programs (circuits)

A *straight-line program* is a list of gates; the gate at position `j` computes the
value of wire `j` from input bits and from wires with smaller index.  This is the
standard (fan-in two) Boolean circuit model, presented in a topologically sorted way.
-/

namespace Frontier

/-- A single gate of a straight-line program.  `neg`, `conj`, `disj` refer to
previously computed wires; `inp i` reads input bit `i`; `cst b` is a constant. -/
inductive Gate
  | inp (i : ℕ)
  | cst (b : Bool)
  | neg (a : ℕ)
  | conj (a b : ℕ)
  | disj (a b : ℕ)
deriving DecidableEq, Repr

/-- A straight-line program (Boolean circuit) is a list of gates. -/
abbrev SLP := List Gate

/-- Value of a gate given the input bits `x` and the values `vs` of earlier wires. -/
def evalGate (x : ℕ → Bool) (vs : List Bool) : Gate → Bool
  | .inp i => x i
  | .cst b => b
  | .neg a => !(vs.getD a false)
  | .conj a b => (vs.getD a false) && (vs.getD b false)
  | .disj a b => (vs.getD a false) || (vs.getD b false)

/-- The step function used to evaluate a straight-line program. -/
def wireStep (x : ℕ → Bool) (vs : List Bool) (g : Gate) : List Bool :=
  vs ++ [evalGate x vs g]

/-- The list of all wire values of a straight-line program. -/
def evalWires (x : ℕ → Bool) (gs : SLP) : List Bool :=
  gs.foldl (wireStep x) []

/-- The value of wire `j`. -/
def wireVal (x : ℕ → Bool) (gs : SLP) (j : ℕ) : Bool := (evalWires x gs).getD j false

/-- Well-formedness of the gate at position `j`: it only refers to earlier wires. -/
def Gate.refsLT (j : ℕ) : Gate → Prop
  | .inp _ => True
  | .cst _ => True
  | .neg a => a < j
  | .conj a b => a < j ∧ b < j
  | .disj a b => a < j ∧ b < j

/-- All input bits read by the gate have index `< n`. -/
def Gate.inpLT (n : ℕ) : Gate → Prop
  | .inp i => i < n
  | _ => True

/-- A straight-line program is well-formed if every gate refers only to earlier wires. -/
def WF (gs : SLP) : Prop := ∀ j, ∀ h : j < gs.length, (gs[j]'h).refsLT j

/-- The program reads only input bits of index `< n`. -/
def InputsLT (n : ℕ) (gs : SLP) : Prop := ∀ j, ∀ h : j < gs.length, (gs[j]'h).inpLT n

/-! ### Basic evaluation lemmas -/

lemma foldl_wireStep_grow (x : ℕ → Bool) :
    ∀ (gs : SLP) (acc : List Bool), ∃ ts, gs.foldl (wireStep x) acc = acc ++ ts := by
  intro gs
  induction gs with
  | nil => intro acc; exact ⟨[], by simp⟩
  | cons g gs ih =>
      intro acc
      obtain ⟨ts, hts⟩ := ih (wireStep x acc g)
      refine ⟨evalGate x acc g :: ts, ?_⟩
      rw [List.foldl_cons, hts]
      simp [wireStep]

lemma evalWires_length (x : ℕ → Bool) (gs : SLP) :
    (evalWires x gs).length = gs.length := by
  simp only [evalWires]
  suffices h : ∀ (gs : SLP) (acc : List Bool),
      (gs.foldl (wireStep x) acc).length = acc.length + gs.length by
    simpa using h gs []
  intro gs
  induction gs with
  | nil => intro acc; simp
  | cons g gs ih => intro acc; simp [ih, wireStep]; omega

lemma evalWires_append (x : ℕ → Bool) (gs hs : SLP) :
    ∃ ts, evalWires x (gs ++ hs) = evalWires x gs ++ ts := by
  simp only [evalWires, List.foldl_append]
  exact foldl_wireStep_grow x hs _

lemma evalWires_take_prefix (x : ℕ → Bool) (gs : SLP) (j : ℕ) :
    ∃ ts, evalWires x gs = evalWires x (gs.take j) ++ ts := by
  have := evalWires_append x (gs.take j) (gs.drop j)
  rwa [List.take_append_drop] at this

lemma getD_of_prefix {L P T : List Bool} (h : L = P ++ T) {a : ℕ} (ha : a < P.length) :
    L.getD a false = P.getD a false := by
  subst h
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left ha]

/-- Wire values below index `j` are already determined by the first `j` gates. -/
lemma wireVal_take (x : ℕ → Bool) (gs : SLP) {a j : ℕ} (ha : a < j) (haj : j ≤ gs.length) :
    wireVal x gs a = wireVal x (gs.take j) a := by
  obtain ⟨ts, hts⟩ := evalWires_take_prefix x gs j
  have hlen : (evalWires x (gs.take j)).length = j := by
    rw [evalWires_length, List.length_take]; omega
  exact getD_of_prefix hts (by omega)

/-- Unfolding lemma: the value of wire `j` is obtained by applying gate `j` to the
values of the earlier wires. -/
lemma wireVal_eq_evalGate (x : ℕ → Bool) {gs : SLP} (hwf : WF gs) {j : ℕ}
    (hj : j < gs.length) :
    wireVal x gs j = evalGate x (evalWires x gs) (gs[j]'hj) := by
  have htake : gs.take (j + 1) = gs.take j ++ [gs[j]'hj] := by
    rw [List.take_add_one]
    congr 1
    simp [List.getElem?_eq_getElem hj]
  have hEval : evalWires x (gs.take (j+1))
      = evalWires x (gs.take j) ++ [evalGate x (evalWires x (gs.take j)) (gs[j]'hj)] := by
    rw [htake]
    simp only [evalWires, List.foldl_append, List.foldl_cons, List.foldl_nil, wireStep]
  have hlen : (evalWires x (gs.take j)).length = j := by
    rw [evalWires_length, List.length_take]; omega
  -- value of wire j computed inside the prefix of length j+1
  have h1 : wireVal x gs j = wireVal x (gs.take (j+1)) j :=
    wireVal_take x gs (by omega) (by omega)
  have h2 : wireVal x (gs.take (j+1)) j = evalGate x (evalWires x (gs.take j)) (gs[j]'hj) := by
    simp only [wireVal, hEval, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
  -- the gate only refers to earlier wires, whose values agree with those in the prefix
  have hrefs := hwf j hj
  have key : evalGate x (evalWires x (gs.take j)) (gs[j]'hj)
      = evalGate x (evalWires x gs) (gs[j]'hj) := by
    have hstab : ∀ a, a < j → (evalWires x (gs.take j))[a]?.getD false
        = (evalWires x gs)[a]?.getD false := by
      intro a ha
      simpa [List.getD_eq_getElem?_getD] using (wireVal_take x gs ha (by omega)).symm
    cases hg : (gs[j]'hj) with
    | inp i => simp [evalGate]
    | cst b => simp [evalGate]
    | neg a =>
        rw [hg] at hrefs
        simp [evalGate, hstab a hrefs]
    | conj a b =>
        rw [hg] at hrefs
        simp [evalGate, hstab a hrefs.1, hstab b hrefs.2]
    | disj a b =>
        rw [hg] at hrefs
        simp [evalGate, hstab a hrefs.1, hstab b hrefs.2]
  rw [h1, h2, key]

/-! ### Dependence only on the relevant input bits -/

lemma evalWires_congr {x y : ℕ → Bool} {n : ℕ} {gs : SLP}
    (hin : InputsLT n gs) (hxy : ∀ i < n, x i = y i) :
    evalWires x gs = evalWires y gs := by
  suffices h : ∀ (k : ℕ) (gs : SLP), gs.length ≤ k → InputsLT n gs →
      evalWires x gs = evalWires y gs from h gs.length gs le_rfl hin
  intro k
  induction k with
  | zero =>
      intro gs hk _
      have : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this, evalWires]
  | succ k ih =>
      intro gs hk hin
      rcases List.eq_nil_or_concat gs with h | ⟨gs', g, h⟩
      · simp [h, evalWires]
      · rw [List.concat_eq_append] at h
        subst h
        have hlen : gs'.length ≤ k := by
          simp at hk; omega
        have hin' : InputsLT n gs' := by
          intro j hj
          have hj' : j < (gs' ++ [g]).length := by simp; omega
          have := hin j hj'
          rwa [List.getElem_append_left hj] at this
        have hgin : g.inpLT n := by
          have hj' : gs'.length < (gs' ++ [g]).length := by simp
          have h2 := hin gs'.length hj'
          rw [List.getElem_append_right (by omega)] at h2
          simpa using h2
        have hrec := ih gs' hlen hin'
        have hgate : evalGate x (evalWires x gs') g = evalGate y (evalWires y gs') g := by
          cases hg : g with
          | inp i =>
              rw [hg] at hgin
              simp [evalGate, hxy i hgin]
          | cst b => simp [evalGate]
          | neg a => simp [evalGate, hrec]
          | conj a b => simp [evalGate, hrec]
          | disj a b => simp [evalGate, hrec]
        simp only [evalWires, List.foldl_append, List.foldl_cons, List.foldl_nil, wireStep]
        simp only [evalWires] at hrec hgate
        rw [hgate, hrec]

lemma wireVal_congr {x y : ℕ → Bool} {n : ℕ} {gs : SLP} (hin : InputsLT n gs)
    (hxy : ∀ i < n, x i = y i) (j : ℕ) : wireVal x gs j = wireVal y gs j := by
  simp [wireVal, evalWires_congr hin hxy]

end Frontier

import RequestProject.CookLevin

/-!
# Sanity checks and examples

This file checks that the notions introduced are non-vacuous: we exhibit a concrete
verifier (hence a concrete language in NP), and we sanity-check the Tseitin reduction
on small circuits by brute-force search over assignments.
-/

namespace Frontier

/-! ### A concrete verifier -/

/-- A verifier (with empty witness) for the language of bit strings whose first bit
is `true`. -/
def firstBitVerifier : Verifier where
  wit := fun _ => 0
  ckt := fun n => if n = 0 then [Gate.cst false] else [Gate.inp 0]
  wf := by
    intro n j hj
    have hlen : (if n = 0 then [Gate.cst false] else [Gate.inp 0] : SLP).length = 1 := by
      by_cases hn : n = 0 <;> simp [hn]
    have hj0 : j = 0 := by rw [hlen] at hj; omega
    subst hj0
    by_cases hn : n = 0 <;> simp [hn, Gate.refsLT]
  ne := by
    intro n
    by_cases hn : n = 0 <;> simp [hn]
  reads := by
    intro n j hj
    have hlen : (if n = 0 then [Gate.cst false] else [Gate.inp 0] : SLP).length = 1 := by
      by_cases hn : n = 0 <;> simp [hn]
    have hj0 : j = 0 := by rw [hlen] at hj; omega
    subst hj0
    by_cases hn : n = 0
    · simp [hn, Gate.inpLT]
    · simp only [hn, if_false, List.getElem_cons_zero, Gate.inpLT]
      omega
  polyC := ⟨1, 0, by intro n; by_cases hn : n = 0 <;> simp [hn]⟩
  polyW := ⟨0, 0, by intro n; simp⟩

lemma firstBitVerifier_lang (x : List Bool) :
    firstBitVerifier.lang x ↔ x.getD 0 false = true := by
  constructor
  · rintro ⟨w, hw, hacc⟩
    have hwnil : w = [] := List.eq_nil_of_length_eq_zero (by simpa [firstBitVerifier] using hw)
    subst hwnil
    rcases Nat.eq_zero_or_pos x.length with h | h
    · have : x = [] := List.eq_nil_of_length_eq_zero h
      subst this
      simp [Verifier.accepts, firstBitVerifier, wireVal, evalWires, wireStep, evalGate] at hacc
    · have hn : ¬ x.length = 0 := by omega
      simp only [Verifier.accepts, firstBitVerifier, hn, if_false] at hacc
      simpa [wireVal, evalWires, wireStep, evalGate, assignOf,
        List.getD_eq_getElem?_getD, List.getElem?_append_left h] using hacc
  · intro hx
    have h : 0 < x.length := by
      by_contra hcon
      have : x = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp at hx
    have hn : ¬ x.length = 0 := by omega
    refine ⟨[], by simp [firstBitVerifier], ?_⟩
    simp only [Verifier.accepts, firstBitVerifier, hn, if_false]
    simpa [wireVal, evalWires, wireStep, evalGate, assignOf,
      List.getD_eq_getElem?_getD, List.getElem?_append_left h] using hx

/-- The language of bit strings starting with `true` is in NP. -/
theorem inNP_firstBit : InNP (fun x : List Bool => x.getD 0 false = true) :=
  ⟨firstBitVerifier, fun x => (firstBitVerifier_lang x).symm⟩

/-- Consequently it many-one reduces to SAT. -/
theorem firstBit_reduces_to_SAT (x : List Bool) :
    x.getD 0 false = true ↔ SAT (cookReduction firstBitVerifier x) :=
  (firstBitVerifier_lang x).symm.trans (sat_cookReduction_iff firstBitVerifier x).symm

/-! ### Brute-force checks of the reduction on a small circuit -/

/-- The circuit computing the conjunction of input bits 0 and 1. -/
def andCircuit : SLP := [Gate.inp 0, Gate.inp 1, Gate.conj 0 1]

/-- Brute-force satisfiability check over all assignments to variables `< numVars F`. -/
def bruteSAT (F : CNF) : Bool :=
  (List.range (2 ^ numVars F)).any fun m =>
    evalCNF (fun i => (m / 2 ^ i) % 2 == 1) F

-- The reduction is satisfiable exactly when the hard-wired input bits make the
-- circuit output `true`.
/-- info: true -/
#guard_msgs in
#eval bruteSAT (reduceSLP andCircuit [true, true])

/-- info: false -/
#guard_msgs in
#eval bruteSAT (reduceSLP andCircuit [true, false])

/-- info: false -/
#guard_msgs in
#eval bruteSAT (reduceSLP andCircuit [false, false])

/-- info: true -/
#guard_msgs in
#eval bruteSAT (reduceSLP andCircuit [])

end Frontier

import Mathlib
import RequestProject.CookLevin
import RequestProject.Examples

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

/-! # Cook-Levin: SAT is NP-complete

The development is split across the files
`RequestProject/CNF.lean`, `RequestProject/SLP.lean`, `RequestProject/Tseitin.lean`,
`RequestProject/CookLevin.lean` and `RequestProject/Examples.lean`.
The main theorem is `Frontier.cook_levin`. -/

#print axioms Frontier.cook_levin

import RequestProject.SLP

/-!
# The Tseitin transformation: circuits to CNF

Given a straight-line program (Boolean circuit) `gs` and a list `bits` of fixed values
for its first input bits, we build in linear time a CNF formula `reduceSLP gs bits`
which is satisfiable if and only if some completion of the input makes the circuit
output `true`.  This is the combinatorial heart of the Cook–Levin theorem.

Variables of the produced formula: `wireVar j = 2 * j` stands for the value of wire
`j` of the circuit, and `inputVar i = 2 * i + 1` for input bit `i`.
-/

namespace Frontier

/-- CNF variable holding the value of wire `j`. -/
def wireVar (j : ℕ) : ℕ := 2 * j

/-- CNF variable holding input bit `i`. -/
def inputVar (i : ℕ) : ℕ := 2 * i + 1

/-- Positive literal. -/
def posLit (v : ℕ) : Lit := ⟨v, false⟩

/-- Negative literal. -/
def negLit (v : ℕ) : Lit := ⟨v, true⟩

/-- The clauses defining the value of wire `j`, whose gate is `g`. -/
def tseitinGate (j : ℕ) : Gate → CNF
  | .inp i => [[negLit (wireVar j), posLit (inputVar i)],
               [posLit (wireVar j), negLit (inputVar i)]]
  | .cst b => if b then [[posLit (wireVar j)]] else [[negLit (wireVar j)]]
  | .neg a => [[negLit (wireVar j), negLit (wireVar a)],
               [posLit (wireVar j), posLit (wireVar a)]]
  | .conj a b => [[negLit (wireVar j), posLit (wireVar a)],
                  [negLit (wireVar j), posLit (wireVar b)],
                  [posLit (wireVar j), negLit (wireVar a), negLit (wireVar b)]]
  | .disj a b => [[posLit (wireVar j), negLit (wireVar a)],
                  [posLit (wireVar j), negLit (wireVar b)],
                  [negLit (wireVar j), posLit (wireVar a), posLit (wireVar b)]]

/-- The value a gate should take under a CNF assignment. -/
def gateSem (σ : ℕ → Bool) : Gate → Bool
  | .inp i => σ (inputVar i)
  | .cst b => b
  | .neg a => !(σ (wireVar a))
  | .conj a b => (σ (wireVar a)) && (σ (wireVar b))
  | .disj a b => (σ (wireVar a)) || (σ (wireVar b))

/-- The defining clauses of a gate say exactly that the wire variable carries the
value of the gate. -/
lemma tseitinGate_spec (σ : ℕ → Bool) (j : ℕ) (g : Gate) :
    evalCNF σ (tseitinGate j g) = true ↔ σ (wireVar j) = gateSem σ g := by
  cases g with
  | inp i =>
      simp only [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil]
      cases σ (wireVar j) <;> cases σ (inputVar i) <;> simp
  | cst b =>
      cases b <;> cases hσ : σ (wireVar j) <;>
        simp [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit, hσ]
  | neg a =>
      simp only [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil]
      cases σ (wireVar j) <;> cases σ (wireVar a) <;> simp
  | conj a b =>
      simp only [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil]
      cases σ (wireVar j) <;> cases σ (wireVar a) <;> cases σ (wireVar b) <;> simp
  | disj a b =>
      simp only [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil]
      cases σ (wireVar j) <;> cases σ (wireVar a) <;> cases σ (wireVar b) <;> simp

/-- The Tseitin encoding of a straight-line program. -/
def tseitin (gs : SLP) : CNF :=
  (List.range gs.length).flatMap (fun j => tseitinGate j (gs.getD j (Gate.cst false)))

lemma tseitin_spec (σ : ℕ → Bool) (gs : SLP) :
    evalCNF σ (tseitin gs) = true ↔
      ∀ j, j < gs.length → evalCNF σ (tseitinGate j (gs.getD j (Gate.cst false))) = true := by
  constructor
  · intro h j hj
    rw [evalCNF_eq_true_iff] at h ⊢
    intro C hC
    refine h C ?_
    simp only [tseitin, List.mem_flatMap, List.mem_range]
    exact ⟨j, hj, hC⟩
  · intro h
    rw [evalCNF_eq_true_iff]
    intro C hC
    simp only [tseitin, List.mem_flatMap, List.mem_range] at hC
    obtain ⟨j, hj, hC⟩ := hC
    exact (evalCNF_eq_true_iff _ _).1 (h j hj) C hC

lemma getD_eq_getElem (gs : SLP) {j : ℕ} (hj : j < gs.length) :
    gs.getD j (Gate.cst false) = gs[j]'hj := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- **Soundness**: any assignment satisfying the Tseitin clauses assigns to each wire
variable the true value of that wire, computed from the input variables. -/
lemma tseitin_sound {gs : SLP} (hwf : WF gs) {σ : ℕ → Bool}
    (h : evalCNF σ (tseitin gs) = true) :
    ∀ j, j < gs.length → σ (wireVar j) = wireVal (fun i => σ (inputVar i)) gs j := by
  set x : ℕ → Bool := fun i => σ (inputVar i) with hx
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hj
      have hgate : σ (wireVar j) = gateSem σ (gs[j]'hj) := by
        have := (tseitin_spec σ gs).1 h j hj
        rw [getD_eq_getElem gs hj] at this
        exact (tseitinGate_spec σ j (gs[j]'hj)).1 this
      have hunfold : wireVal x gs j = evalGate x (evalWires x gs) (gs[j]'hj) :=
        wireVal_eq_evalGate x hwf hj
      have hrefs := hwf j hj
      have hwv : ∀ a, a < j → σ (wireVar a) = (evalWires x gs).getD a false := by
        intro a ha
        exact ih a ha (by omega)
      rw [hgate, hunfold]
      cases hg : (gs[j]'hj) with
      | inp i => simp [gateSem, evalGate, hx]
      | cst b => simp [gateSem, evalGate]
      | neg a =>
          rw [hg] at hrefs
          simp [gateSem, evalGate, hwv a hrefs]
      | conj a b =>
          rw [hg] at hrefs
          simp [gateSem, evalGate, hwv a hrefs.1, hwv b hrefs.2]
      | disj a b =>
          rw [hg] at hrefs
          simp [gateSem, evalGate, hwv a hrefs.1, hwv b hrefs.2]

/-- The canonical assignment associated with an input: wire variables get the true
wire values, input variables get the input bits. -/
def canonAssign (x : ℕ → Bool) (gs : SLP) : ℕ → Bool :=
  fun v => if v % 2 = 0 then wireVal x gs (v / 2) else x (v / 2)

@[simp] lemma canonAssign_wireVar (x : ℕ → Bool) (gs : SLP) (j : ℕ) :
    canonAssign x gs (wireVar j) = wireVal x gs j := by
  simp [canonAssign, wireVar, Nat.mul_mod_right]

@[simp] lemma canonAssign_inputVar (x : ℕ → Bool) (gs : SLP) (i : ℕ) :
    canonAssign x gs (inputVar i) = x i := by
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [canonAssign, inputVar, h1, h2]

/-- **Completeness**: the canonical assignment satisfies the Tseitin clauses. -/
lemma canonAssign_sat {gs : SLP} (hwf : WF gs) (x : ℕ → Bool) :
    evalCNF (canonAssign x gs) (tseitin gs) = true := by
  rw [tseitin_spec]
  intro j hj
  rw [getD_eq_getElem gs hj, tseitinGate_spec]
  rw [canonAssign_wireVar, wireVal_eq_evalGate x hwf hj]
  cases hg : (gs[j]'hj) with
  | inp i => simp [gateSem, evalGate]
  | cst b => simp [gateSem, evalGate]
  | neg a => simp [gateSem, evalGate, wireVal]
  | conj a b => simp [gateSem, evalGate, wireVal]
  | disj a b => simp [gateSem, evalGate, wireVal]

/-! ### Fixing the first input bits -/

/-- Unit clauses forcing input variable `i` to take the value `bits[i]`. -/
def fixClauses (bits : List Bool) : CNF :=
  (List.range bits.length).map (fun i => [Lit.mk (inputVar i) (!(bits.getD i false))])

lemma fixClauses_spec (σ : ℕ → Bool) (bits : List Bool) :
    evalCNF σ (fixClauses bits) = true ↔ ∀ i, i < bits.length → σ (inputVar i) = bits.getD i false := by
  rw [evalCNF_eq_true_iff]
  constructor
  · intro h i hi
    have := h _ (by
      simp only [fixClauses, List.mem_map, List.mem_range]
      exact ⟨i, hi, rfl⟩)
    simp only [evalClause, evalLit, List.any_cons, List.any_nil] at this
    revert this
    cases σ (inputVar i) <;> cases hb : bits.getD i false <;> simp
  · intro h C hC
    simp only [fixClauses, List.mem_map, List.mem_range] at hC
    obtain ⟨i, hi, rfl⟩ := hC
    simp only [evalClause, evalLit, List.any_cons, List.any_nil]
    rw [h i hi]
    cases bits.getD i false <;> simp

/-! ### The reduction -/

/-- The CNF formula produced from a circuit `gs` together with fixed values `bits`
for its first input bits: it is satisfiable iff the circuit can output `true`. -/
def reduceSLP (gs : SLP) (bits : List Bool) : CNF :=
  tseitin gs ++ fixClauses bits ++ [[posLit (wireVar (gs.length - 1))]]

/-- **Correctness of the Tseitin reduction.** -/
theorem sat_reduceSLP_iff {gs : SLP} (hwf : WF gs) (hne : gs ≠ []) (bits : List Bool) :
    SAT (reduceSLP gs bits) ↔
      ∃ x : ℕ → Bool, (∀ i, i < bits.length → x i = bits.getD i false) ∧
        wireVal x gs (gs.length - 1) = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    simp only [reduceSLP, evalCNF_append, Bool.and_eq_true] at hσ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hσ
    refine ⟨fun i => σ (inputVar i), ?_, ?_⟩
    · exact (fixClauses_spec σ bits).1 h2
    · have hlen : 0 < gs.length := List.length_pos_iff.2 hne
      have hj : gs.length - 1 < gs.length := by omega
      have := tseitin_sound hwf h1 (gs.length - 1) hj
      rw [← this]
      simpa [evalCNF, evalClause, evalLit, posLit] using h3
  · rintro ⟨x, hbits, hout⟩
    refine ⟨canonAssign x gs, ?_⟩
    simp only [reduceSLP, evalCNF_append, Bool.and_eq_true]
    refine ⟨⟨canonAssign_sat hwf x, ?_⟩, ?_⟩
    · rw [fixClauses_spec]
      intro i hi
      rw [canonAssign_inputVar]
      exact hbits i hi
    · simp [evalCNF, evalClause, evalLit, posLit, hout]

/-! ### Size of the reduction -/

lemma cnfSize_flatMap {α : Type*} (l : List α) (f : α → CNF) :
    cnfSize (l.flatMap f) = (l.map (fun a => cnfSize (f a))).sum := by
  induction l with
  | nil => simp [cnfSize]
  | cons a l ih => simp [List.flatMap_cons, cnfSize_append, ih]

lemma cnfSize_tseitinGate (j : ℕ) (g : Gate) : cnfSize (tseitinGate j g) ≤ 10 := by
  cases g with
  | inp i => simp [tseitinGate, cnfSize]
  | cst b => cases b <;> simp [tseitinGate, cnfSize]
  | neg a => simp [tseitinGate, cnfSize]
  | conj a b => simp [tseitinGate, cnfSize]
  | disj a b => simp [tseitinGate, cnfSize]

lemma cnfSize_tseitin (gs : SLP) : cnfSize (tseitin gs) ≤ 10 * gs.length := by
  rw [tseitin, cnfSize_flatMap]
  have : ∀ n : ℕ, ((List.range n).map
      (fun j => cnfSize (tseitinGate j (gs.getD j (Gate.cst false))))).sum ≤ 10 * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append]
        have := cnfSize_tseitinGate n (gs.getD n (Gate.cst false))
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        omega
  exact this gs.length

lemma cnfSize_fixClauses (bits : List Bool) : cnfSize (fixClauses bits) = 2 * bits.length := by
  simp only [cnfSize, fixClauses, List.length_map, List.length_range, List.map_map,
    Function.comp_def, List.length_cons, List.length_nil]
  simp [two_mul]

/-- The reduction produces a formula of size linear in the size of the circuit and
of the fixed input, so it is computable in polynomial (indeed linear) time. -/
theorem cnfSize_reduceSLP (gs : SLP) (bits : List Bool) :
    cnfSize (reduceSLP gs bits) ≤ 10 * gs.length + 2 * bits.length + 2 := by
  simp only [reduceSLP, cnfSize_append, cnfSize_fixClauses]
  have h1 := cnfSize_tseitin gs
  have h2 : cnfSize [[posLit (wireVar (gs.length - 1))]] = 2 := by simp [cnfSize]
  omega

/-! ### A cost-instrumented construction of the reduction

The reduction is not merely of polynomial size: it is *computed* in linear time.  We
make this precise with an explicitly instrumented algorithm building the formula,
charging a constant number of elementary steps per gate of the circuit and per fixed
input bit. -/

/-- Cost-instrumented construction of the Tseitin clauses of `gs`, whose first gate
has index `j`. -/
def tseitinBuild : ℕ → SLP → CNF × ℕ
  | _, [] => ([], 1)
  | j, g :: gs => let r := tseitinBuild (j + 1) gs; (tseitinGate j g ++ r.1, r.2 + 11)

lemma tseitinBuild_fst (j : ℕ) (gs : SLP) :
    (tseitinBuild j gs).1 =
      (List.range gs.length).flatMap
        (fun i => tseitinGate (j + i) (gs.getD i (Gate.cst false))) := by
  induction gs generalizing j with
  | nil => simp [tseitinBuild]
  | cons g gs ih =>
      simp only [tseitinBuild, List.length_cons, ih (j + 1)]
      rw [List.range_succ_eq_map]
      simp only [List.flatMap_cons, List.flatMap_map]
      congr 1
      refine List.flatMap_congr ?_
      intro i _
      congr 1
      omega

lemma tseitinBuild_snd (j : ℕ) (gs : SLP) : (tseitinBuild j gs).2 = 11 * gs.length + 1 := by
  induction gs generalizing j with
  | nil => simp [tseitinBuild]
  | cons g gs ih => simp only [tseitinBuild, List.length_cons, ih (j + 1)]; omega

lemma tseitinBuild_zero (gs : SLP) : (tseitinBuild 0 gs).1 = tseitin gs := by
  rw [tseitinBuild_fst, tseitin]
  simp

/-- The cost-instrumented construction of the whole reduction. -/
def reduceBuild (gs : SLP) (bits : List Bool) : CNF × ℕ :=
  let t := tseitinBuild 0 gs
  (t.1 ++ fixClauses bits ++ [[posLit (wireVar (gs.length - 1))]],
    t.2 + 2 * bits.length + 2)

@[simp] theorem reduceBuild_fst (gs : SLP) (bits : List Bool) :
    (reduceBuild gs bits).1 = reduceSLP gs bits := by
  simp [reduceBuild, reduceSLP, tseitinBuild_zero]

/-- The construction runs in linear time in the size of the circuit and of the input. -/
theorem reduceBuild_snd (gs : SLP) (bits : List Bool) :
    (reduceBuild gs bits).2 = 11 * gs.length + 2 * bits.length + 3 := by
  simp only [reduceBuild, tseitinBuild_snd]
  omega

end Frontier

