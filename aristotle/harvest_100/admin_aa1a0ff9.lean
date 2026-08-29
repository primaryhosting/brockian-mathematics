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
# A relativized model of computation

We formalise oracle computation by a small imperative register language over bit
strings.  Registers hold finite bit strings (`List Bool`), and a program may query
an oracle (an arbitrary set of bit strings, presented as `Str → Bool`).

The cost model is: each elementary instruction costs one unit, except copying and
querying, which cost one unit plus the length of the string that is moved / written
on the query tape.  This is the usual convention for oracle Turing machines: writing
the query string on the oracle tape takes as many steps as the string is long.
-/

set_option autoImplicit false

namespace BGS

/-- Bit strings. -/
abbrev Str := List Bool

/-- An oracle is an arbitrary set of bit strings. -/
abbrev Oracle := Str → Bool

/-- A language is a set of bit strings. -/
abbrev Lang := Set Str

/-- A register store: countably many registers, each holding a bit string. -/
abbrev St := ℕ → Str

/-- Update one register. -/
def upd (st : St) (r : ℕ) (v : Str) : St := fun i => if i = r then v else st i

@[simp] lemma upd_self (st : St) (r : ℕ) (v : Str) : upd st r v r = v := by
  simp [upd]

@[simp] lemma upd_other {i r : ℕ} (st : St) (v : Str) (h : i ≠ r) : upd st r v i = st i := by
  simp [upd, h]

/-- Programs of the oracle register language. -/
inductive Cmd where
  /-- `r := []` -/
  | clear (r : ℕ)
  /-- `r := b :: r` -/
  | push (b : Bool) (r : ℕ)
  /-- `r := r.tail` -/
  | pop (r : ℕ)
  /-- `r := s` -/
  | copy (r s : ℕ)
  /-- `r := [oracle answer on the contents of s]` -/
  | query (r s : ℕ)
  /-- sequential composition -/
  | seq (c d : Cmd)
  /-- `if head r = true then c else d` -/
  | ite (r : ℕ) (c d : Cmd)
  /-- `while r ≠ [] do c` -/
  | wh (r : ℕ) (c : Cmd)
  deriving DecidableEq

deriving instance Countable for Cmd

instance : Inhabited Cmd := ⟨Cmd.clear 0⟩

/-- A configuration: a stack of commands still to be executed, and the store. -/
structure Cfg where
  cont : List Cmd
  st : St

/-- One computation step. -/
def step (O : Oracle) : Cfg → Cfg
  | ⟨[], st⟩ => ⟨[], st⟩
  | ⟨.clear r :: k, st⟩ => ⟨k, upd st r []⟩
  | ⟨.push b r :: k, st⟩ => ⟨k, upd st r (b :: st r)⟩
  | ⟨.pop r :: k, st⟩ => ⟨k, upd st r (st r).tail⟩
  | ⟨.copy r s :: k, st⟩ => ⟨k, upd st r (st s)⟩
  | ⟨.query r s :: k, st⟩ => ⟨k, upd st r [O (st s)]⟩
  | ⟨.seq c d :: k, st⟩ => ⟨c :: d :: k, st⟩
  | ⟨.ite r c d :: k, st⟩ => ⟨(if (st r).head? = some true then c else d) :: k, st⟩
  | ⟨.wh r c :: k, st⟩ => if st r = [] then ⟨k, st⟩ else ⟨c :: Cmd.wh r c :: k, st⟩

/-- The cost of one computation step. -/
def stepCost (cf : Cfg) : ℕ :=
  match cf with
  | ⟨[], _⟩ => 0
  | ⟨.copy _ s :: _, st⟩ => (st s).length + 1
  | ⟨.query _ s :: _, st⟩ => (st s).length + 1
  | ⟨_ :: _, _⟩ => 1

/-- The oracle query (if any) performed by one computation step. -/
def stepQuery (cf : Cfg) : Option Str :=
  match cf with
  | ⟨.query _ s :: _, st⟩ => some (st s)
  | _ => none

/-- The total cost of the first `t` steps. -/
def gasUsed (O : Oracle) (cf : Cfg) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, stepCost ((step O)^[i] cf)

/-- The list of queries performed during the first `t` steps. -/
def queriesUpto (O : Oracle) (cf : Cfg) (t : ℕ) : List Str :=
  (List.range t).filterMap (fun i => stepQuery ((step O)^[i] cf))

/-- A configuration is halted when there is nothing left to execute. -/
def Halted (cf : Cfg) : Prop := cf.cont = []

instance (cf : Cfg) : Decidable (Halted cf) := by
  unfold Halted; infer_instance

/-! ### Basic properties of the semantics -/

lemma step_halted {O : Oracle} {cf : Cfg} (h : Halted cf) : step O cf = cf := by
  obtain ⟨cont, st⟩ := cf
  simp only [Halted] at h
  subst h
  rfl

lemma stepCost_halted {cf : Cfg} (h : Halted cf) : stepCost cf = 0 := by
  obtain ⟨cont, st⟩ := cf
  simp only [Halted] at h
  subst h
  rfl

lemma stepQuery_halted {cf : Cfg} (h : Halted cf) : stepQuery cf = none := by
  obtain ⟨cont, st⟩ := cf
  simp only [Halted] at h
  subst h
  rfl

lemma stepCost_pos {cf : Cfg} (h : ¬ Halted cf) : 1 ≤ stepCost cf := by
  obtain ⟨cont, st⟩ := cf
  simp only [Halted] at h
  match cont with
  | [] => exact absurd rfl h
  | .clear _ :: _ => simp [stepCost]
  | .push _ _ :: _ => simp [stepCost]
  | .pop _ :: _ => simp [stepCost]
  | .copy _ _ :: _ => simp [stepCost]
  | .query _ _ :: _ => simp [stepCost]
  | .seq _ _ :: _ => simp [stepCost]
  | .ite _ _ _ :: _ => simp [stepCost]
  | .wh _ _ :: _ => simp [stepCost]

lemma iterate_halted {O : Oracle} {cf : Cfg} (h : Halted cf) (t : ℕ) :
    (step O)^[t] cf = cf := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', ih, step_halted h]

lemma halted_mono {O : Oracle} {cf : Cfg} {t t' : ℕ} (htt : t ≤ t')
    (h : Halted ((step O)^[t] cf)) : Halted ((step O)^[t'] cf) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htt
  rw [Function.iterate_add_apply, iterate_halted h d]
  exact h

lemma gasUsed_add (O : Oracle) (cf : Cfg) (a b : ℕ) :
    gasUsed O cf (a + b) = gasUsed O cf a + gasUsed O ((step O)^[a] cf) b := by
  unfold gasUsed
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Function.iterate_add_apply]
  congr 1
  omega

lemma gasUsed_mono (O : Oracle) (cf : Cfg) {a b : ℕ} (h : a ≤ b) :
    gasUsed O cf a ≤ gasUsed O cf b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [gasUsed_add]
  omega

lemma gasUsed_succ (O : Oracle) (cf : Cfg) (t : ℕ) :
    gasUsed O cf (t + 1) = gasUsed O cf t + stepCost ((step O)^[t] cf) := by
  rw [gasUsed_add]
  simp [gasUsed]

lemma le_gasUsed_of_not_halted {O : Oracle} {cf : Cfg} {t : ℕ}
    (h : ¬ Halted ((step O)^[t] cf)) : t ≤ gasUsed O cf t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h' : ¬ Halted ((step O)^[t] cf) := fun hc => h (halted_mono (Nat.le_succ t) hc)
      have h2 := ih h'
      rw [gasUsed_succ]
      have h3 := stepCost_pos h'
      omega

/-- If a computation halts within gas `G`, then it is already halted after `G` steps. -/
lemma halted_at_gas {O : Oracle} {cf : Cfg} {t G : ℕ}
    (ht : Halted ((step O)^[t] cf)) (hg : gasUsed O cf t ≤ G) :
    Halted ((step O)^[G] cf) := by
  by_cases hGt : t ≤ G
  · exact halted_mono hGt ht
  · push_neg at hGt
    by_contra hc
    have h1 : G ≤ gasUsed O cf G := le_gasUsed_of_not_halted hc
    have h2 : gasUsed O cf (G + 1) = gasUsed O cf G + stepCost ((step O)^[G] cf) :=
      gasUsed_succ O cf G
    have h3 : 1 ≤ stepCost ((step O)^[G] cf) := stepCost_pos hc
    have h4 : gasUsed O cf (G + 1) ≤ gasUsed O cf t := gasUsed_mono O cf (by omega)
    omega

/-! ### Queries -/

lemma stepQuery_cost {cf : Cfg} {q : Str} (h : stepQuery cf = some q) :
    stepCost cf = q.length + 1 := by
  obtain ⟨cont, st⟩ := cf
  match cont with
  | [] => simp [stepQuery] at h
  | .clear _ :: _ => simp [stepQuery] at h
  | .push _ _ :: _ => simp [stepQuery] at h
  | .pop _ :: _ => simp [stepQuery] at h
  | .copy _ _ :: _ => simp [stepQuery] at h
  | .query _ s :: _ =>
      simp only [stepQuery, Option.some.injEq] at h
      subst h
      simp [stepCost]
  | .seq _ _ :: _ => simp [stepQuery] at h
  | .ite _ _ _ :: _ => simp [stepQuery] at h
  | .wh _ _ :: _ => simp [stepQuery] at h

lemma step_congr (O O' : Oracle) (cf : Cfg)
    (h : ∀ q, stepQuery cf = some q → O q = O' q) : step O cf = step O' cf := by
  obtain ⟨cont, st⟩ := cf
  match cont with
  | [] => rfl
  | .clear _ :: _ => rfl
  | .push _ _ :: _ => rfl
  | .pop _ :: _ => rfl
  | .copy _ _ :: _ => rfl
  | .query r s :: k =>
      have := h (st s) rfl
      simp [step, this]
  | .seq _ _ :: _ => rfl
  | .ite _ _ _ :: _ => rfl
  | .wh _ _ :: _ => rfl

lemma queriesUpto_succ (O : Oracle) (cf : Cfg) (t : ℕ) :
    queriesUpto O cf (t + 1) =
      queriesUpto O cf t ++ (stepQuery ((step O)^[t] cf)).toList := by
  unfold queriesUpto
  rw [List.range_succ, List.filterMap_append]
  cases h : stepQuery ((step O)^[t] cf) <;> simp [h]

lemma mem_queriesUpto {O : Oracle} {cf : Cfg} {t : ℕ} {q : Str}
    (h : q ∈ queriesUpto O cf t) : ∃ i < t, stepQuery ((step O)^[i] cf) = some q := by
  unfold queriesUpto at h
  rw [List.mem_filterMap] at h
  obtain ⟨i, hi, hq⟩ := h
  exact ⟨i, by simpa using List.mem_range.1 hi, hq⟩

lemma queriesUpto_mem {O : Oracle} {cf : Cfg} {t : ℕ} {q : Str} {i : ℕ} (hi : i < t)
    (hq : stepQuery ((step O)^[i] cf) = some q) : q ∈ queriesUpto O cf t := by
  unfold queriesUpto
  rw [List.mem_filterMap]
  exact ⟨i, List.mem_range.2 hi, hq⟩

lemma queries_length_lt {O : Oracle} {cf : Cfg} {t : ℕ} {q : Str}
    (h : q ∈ queriesUpto O cf t) : q.length < gasUsed O cf t := by
  obtain ⟨i, hi, hq⟩ := mem_queriesUpto h
  have hc : stepCost ((step O)^[i] cf) = q.length + 1 := stepQuery_cost hq
  have hle : stepCost ((step O)^[i] cf) ≤ gasUsed O cf t := by
    unfold gasUsed
    exact Finset.single_le_sum (f := fun j => stepCost ((step O)^[j] cf))
      (fun j _ => Nat.zero_le _) (Finset.mem_range.2 hi)
  omega

lemma queries_card {O : Oracle} {cf : Cfg} (t : ℕ) :
    (queriesUpto O cf t).length ≤ gasUsed O cf t := by
  induction t with
  | zero => simp [queriesUpto, gasUsed]
  | succ t ih =>
      rw [queriesUpto_succ, gasUsed_succ, List.length_append]
      cases h : stepQuery ((step O)^[t] cf) with
      | none => simp only [Option.toList_none, List.length_nil]; omega
      | some q =>
          have := stepQuery_cost h
          simp only [Option.toList_some, List.length_cons, List.length_nil]
          omega

/-! ### The use principle -/

lemma run_congr (O O' : Oracle) (cf : Cfg) (t : ℕ)
    (h : ∀ q ∈ queriesUpto O cf t, O q = O' q) :
    (step O)^[t] cf = (step O')^[t] cf ∧ gasUsed O cf t = gasUsed O' cf t ∧
      queriesUpto O cf t = queriesUpto O' cf t := by
  induction t with
  | zero => simp [gasUsed, queriesUpto]
  | succ t ih =>
      have hsub : ∀ q ∈ queriesUpto O cf t, O q = O' q := by
        intro q hq
        exact h q (by rw [queriesUpto_succ]; exact List.mem_append_left _ hq)
      obtain ⟨h1, h2, h3⟩ := ih hsub
      have hstepeq : step O ((step O)^[t] cf) = step O' ((step O')^[t] cf) := by
        rw [← h1]
        refine step_congr O O' _ (fun q hq => h q ?_)
        exact queriesUpto_mem (Nat.lt_succ_self t) hq
      refine ⟨?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstepeq]
      · rw [gasUsed_succ, gasUsed_succ, h1, h2]
      · rw [queriesUpto_succ, queriesUpto_succ, h1, h3]

end BGS

