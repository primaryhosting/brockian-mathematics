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
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The relativization barrier

We formalize the Baker–Gill–Solovay theorem in a *relativized query model* of
computation:

* A **string** is a `List Bool`, a **language** (equivalently an oracle) is a
  Boolean-valued function on strings.
* An **oracle machine** is given by a *computable* transition function
  `step : α × Trans → Str ⊕ Bool`, which, given the input and the transcript of
  the queries asked so far together with the oracle's answers, either asks a new
  query (`Sum.inl z`) or halts with a verdict (`Sum.inr b`).
* The resource that is counted is the number of steps (each step is either one
  oracle query or the final answer), and a machine is *polynomially bounded*
  when it is run for `c * (n+1)^d` steps on inputs of length `n`.

`PClass A` is the class of languages decided by a polynomially bounded
deterministic oracle machine with oracle `A`; `NPClass A` is the class of
languages accepted with a polynomially long certificate by a polynomially
bounded verifier with oracle `A`.

The theorem `CS.baker_gill_solovay` states that there is an oracle `A` with
`PClass A = NPClass A` and an oracle `B` with `PClass B ≠ NPClass B`.

Two features of this model should be kept in mind. Machines are required to be
computable, so there are only countably many of them, which is what makes the
diagonalization for `B` possible; and the amount of computation performed
between two queries is unrestricted, only the number of steps is. Consequently
the collapsing oracle can be taken to be the empty oracle `emptyLang`: with no
useful oracle, both classes consist exactly of the decidable languages, since a
deterministic machine may scan all polynomially long certificates in a single
step. The separating oracle `B` is built by the usual stage construction: at
stage `i` one diagonalizes against the `i`-th machine at a length `N` where the
machine's step bound is smaller than the number `2 ^ N` of candidate strings.
-/

namespace CS

/-- Strings are finite bit sequences. -/
abbrev Str := List Bool

/-- A language, equivalently an oracle, is an indicator function on strings. -/
abbrev Lang := Str → Bool

/-- A transcript records the queries made so far together with their answers. -/
abbrev Trans := List (Str × Bool)

/-- An oracle machine with input type `α`: a computable function which, from the
input and the transcript so far, either issues a new oracle query or halts with
a verdict. -/
structure Machine (α : Type) [Primcodable α] : Type where
  /-- The transition function. -/
  step : α × Trans → Str ⊕ Bool
  /-- The transition function is computable. -/
  hstep : Computable step

section Model

variable {α : Type} [Primcodable α]

/-- A configuration: the input, the transcript so far, and the verdict (if the
machine has already halted). -/
abbrev Config (α : Type) := α × Trans × Option Bool

/-- One step of the machine with oracle `O`. -/
def next (M : Machine α) (O : Lang) (s : Config α) : Config α :=
  match s.2.2 with
  | some _ => s
  | none =>
      match M.step (s.1, s.2.1) with
      | Sum.inl z => (s.1, s.2.1 ++ [(z, O z)], none)
      | Sum.inr b => (s.1, s.2.1, some b)

/-- `k` steps of the machine with oracle `O`. -/
def iter (M : Machine α) (O : Lang) : ℕ → Config α → Config α
  | 0, s => s
  | k + 1, s => next M O (iter M O k s)

/-- The verdict of `M` with oracle `O` on input `a` after `k` steps (`none` if it
has not halted yet). -/
def run (M : Machine α) (O : Lang) (a : α) (k : ℕ) : Option Bool :=
  (iter M O k (a, [], none)).2.2

/-- The list of queries made by `M` with oracle `O` on input `a` within `k` steps. -/
def queries (M : Machine α) (O : Lang) (a : α) (k : ℕ) : List Str :=
  (iter M O k (a, [], none)).2.1.map Prod.fst

/-- The polynomial step bound `c * (n+1)^d`. -/
def polyBound (c d n : ℕ) : ℕ := c * (n + 1) ^ d

end Model

/-- The relativized class `P^A`. -/
def PClass (A : Lang) : Set Lang :=
  {L | ∃ (M : Machine Str) (c d : ℕ), ∀ x : Str,
        run M A x (polyBound c d x.length) = some (L x)}

/-- The relativized class `NP^A`. -/
def NPClass (A : Lang) : Set Lang :=
  {L | ∃ (V : Machine (Str × Str)) (c d : ℕ), ∀ x : Str,
        (L x = true ↔ ∃ y : Str, y.length ≤ polyBound c d x.length ∧
          run V A (x, y) (polyBound c d x.length) = some true)}

/-! ## Basic properties of runs -/

section Runs

variable {α : Type} [Primcodable α]

lemma next_of_halted (M : Machine α) (O : Lang) {s : Config α} {b : Bool}
    (h : s.2.2 = some b) : next M O s = s := by
  simp [next, h]

lemma iter_of_halted (M : Machine α) (O : Lang) {s : Config α} {b : Bool}
    (h : s.2.2 = some b) : ∀ k, iter M O k s = s
  | 0 => rfl
  | k + 1 => by rw [iter, iter_of_halted M O h k, next_of_halted M O h]

lemma next_fst (M : Machine α) (O : Lang) (s : Config α) : (next M O s).1 = s.1 := by
  rcases h : s.2.2 with _ | b
  · rcases hs : M.step (s.1, s.2.1) with z | b <;> simp [next, h, hs]
  · simp [next, h]

lemma iter_fst (M : Machine α) (O : Lang) (s : Config α) (k : ℕ) :
    (iter M O k s).1 = s.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iter, next_fst, ih]

lemma next_trans_prefix (M : Machine α) (O : Lang) (s : Config α) :
    s.2.1 <+: (next M O s).2.1 := by
  rcases hs : s.2.2 with _ | b
  · rcases hstep : M.step (s.1, s.2.1) with z | b <;> simp [next, hs, hstep]
  · simp [next, hs]

lemma next_trans_length (M : Machine α) (O : Lang) (s : Config α) :
    (next M O s).2.1.length ≤ s.2.1.length + 1 := by
  rcases hs : s.2.2 with _ | b
  · rcases hstep : M.step (s.1, s.2.1) with z | b <;> simp [next, hs, hstep]
  · simp [next, hs]

lemma iter_trans_length (M : Machine α) (O : Lang) (s : Config α) (k : ℕ) :
    (iter M O k s).2.1.length ≤ s.2.1.length + k := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
      rw [iter]
      exact le_trans (next_trans_length M O _) (by omega)

lemma queries_length_le (M : Machine α) (O : Lang) (a : α) (k : ℕ) :
    (queries M O a k).length ≤ k := by
  have := iter_trans_length M O (a, ([] : Trans), (none : Option Bool)) k
  simpa [queries] using this

/-- Locality: the run only depends on the oracle's answers to the queries it
actually makes. -/
lemma iter_congr (M : Machine α) (O O' : Lang) : ∀ (k : ℕ) (s : Config α),
    (∀ z ∈ (iter M O k s).2.1.map Prod.fst, O z = O' z) →
    iter M O' k s = iter M O k s
  | 0, s, _ => rfl
  | k + 1, s, h => by
      have hpre : (iter M O k s).2.1 <+: (iter M O (k + 1) s).2.1 := by
        rw [iter]; exact next_trans_prefix M O _
      have IH := iter_congr M O O' k s (fun z hz =>
        h z (List.map_subset _ hpre.subset hz))
      rw [iter, iter, IH]
      set t := iter M O k s with ht'
      rcases ht : t.2.2 with _ | b
      · rcases hstep : M.step (t.1, t.2.1) with z | b
        · have hz : O z = O' z := by
            refine h z ?_
            rw [iter, ← ht']
            simp [next, ht, hstep]
          simp [next, ht, hstep, hz]
        · simp [next, ht, hstep]
      · simp [next, ht]

lemma run_congr (M : Machine α) (O O' : Lang) (a : α) (k : ℕ)
    (h : ∀ z ∈ queries M O a k, O z = O' z) :
    run M O' a k = run M O a k := by
  rw [run, run, iter_congr M O O' k _ h]

end Runs

/-! ## Enumerations of strings -/

/-- All strings of length exactly `n`. -/
def allStr : ℕ → List Str
  | 0 => [[]]
  | n + 1 => (allStr n).flatMap (fun w => [false :: w, true :: w])

/-- All strings of length at most `n`. -/
def allStrLe : ℕ → List Str
  | 0 => [[]]
  | n + 1 => allStrLe n ++ allStr (n + 1)

lemma mem_allStr {w : Str} {n : ℕ} : w ∈ allStr n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [allStr, List.length_eq_zero_iff]
  | succ n ih =>
      simp only [allStr, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨v, hv, rfl | rfl⟩ <;> simp [ih.1 hv]
      · intro hlen
        cases w with
        | nil => simp at hlen
        | cons b v =>
            refine ⟨v, ih.2 (by simpa using hlen), ?_⟩
            cases b <;> simp

lemma mem_allStrLe {w : Str} {n : ℕ} : w ∈ allStrLe n ↔ w.length ≤ n := by
  induction n with
  | zero => simp [allStrLe, List.length_eq_zero_iff]
  | succ n ih =>
      simp only [allStrLe, List.mem_append, ih, mem_allStr]
      omega

/-- A Boolean bounded existential over a list. -/
def existsIn (l : List Str) (p : Str → Bool) : Bool :=
  l.foldr (fun w acc => p w || acc) false

lemma existsIn_eq_true {l : List Str} {p : Str → Bool} :
    existsIn l p = true ↔ ∃ w ∈ l, p w = true := by
  induction l with
  | nil => simp [existsIn]
  | cons a l ih =>
      simp only [existsIn, List.foldr_cons, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
      rw [show List.foldr (fun w acc => p w || acc) false l = existsIn l p from rfl, ih]

/-- There are more than `Q.length` strings of length `N` as soon as
`Q.length < 2 ^ N`, so some string of length `N` avoids `Q`. -/
lemma exists_unqueried (N : ℕ) (Q : List Str) (h : Q.length < 2 ^ N) :
    ∃ w : Str, w.length = N ∧ w ∉ Q := by
  by_contra hc
  push_neg at hc
  classical
  set S : Finset Str := Finset.image (fun f : Fin N → Bool => List.ofFn f) Finset.univ with hS
  have hcard : S.card = 2 ^ N := by
    rw [hS, Finset.card_image_of_injective _ (fun f g hfg => List.ofFn_injective hfg)]
    simp
  have hsub : S ⊆ Q.toFinset := by
    intro w hw
    rw [hS, Finset.mem_image] at hw
    obtain ⟨f, -, rfl⟩ := hw
    simpa using hc _ (by simp)
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le Q
  omega

/-! ## Computability facts -/

section Computability

variable {α : Type} [Primcodable α]

lemma computable_next (M : Machine α) (O : Lang) (hO : Computable O) :
    Computable (next M O) := by
  have hstep : Computable (fun s : Config α => M.step (s.1, s.2.1)) :=
    M.hstep.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
  have hquery : Computable₂ (fun (s : Config α) (z : Str) =>
      ((s.1, s.2.1 ++ [(z, O z)], none) : Config α)) := by
    apply Computable.pair (Computable.fst.comp Computable.fst)
    apply Computable.pair
    · exact Computable.list_append.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.list_cons.comp
          (Computable.pair Computable.snd (hO.comp Computable.snd))
          (Computable.const []))
    · exact Computable.const none
  have hhalt : Computable₂ (fun (s : Config α) (b : Bool) =>
      ((s.1, s.2.1, some b) : Config α)) := by
    apply Computable.pair (Computable.fst.comp Computable.fst)
    exact Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.option_some.comp Computable.snd)
  have hmain : Computable (fun s : Config α =>
      Sum.casesOn (motive := fun _ => Config α) (M.step (s.1, s.2.1))
        (fun z => ((s.1, s.2.1 ++ [(z, O z)], none) : Config α))
        (fun b => ((s.1, s.2.1, some b) : Config α))) :=
    Computable.sumCasesOn hstep hquery hhalt
  refine (Computable.option_casesOn (Computable.snd.comp Computable.snd) hmain
    (show Computable₂ (fun (s : Config α) (_ : Bool) => s) from Computable.fst)).of_eq ?_
  intro s
  rcases hs : s.2.2 with _ | b
  · rcases hstep2 : M.step (s.1, s.2.1) with z | b <;> simp [next, hs, hstep2]
  · simp [next, hs]

lemma computable_run (M : Machine α) (O : Lang) (hO : Computable O) :
    Computable₂ (fun (a : α) (k : ℕ) => run M O a k) := by
  have hiter : Computable (fun p : α × ℕ => iter M O p.2 (p.1, [], none)) := by
    have := Computable.nat_rec (f := fun p : α × ℕ => p.2)
      (g := fun p : α × ℕ => ((p.1, [], none) : Config α))
      (h := fun (_ : α × ℕ) (q : ℕ × Config α) => next M O q.2)
      Computable.snd
      (Computable.pair Computable.fst (Computable.pair (Computable.const [])
        (Computable.const none)))
      ((computable_next M O hO).comp (Computable.snd.comp Computable.snd))
    refine this.of_eq ?_
    rintro ⟨a, k⟩
    simp only
    induction k with
    | zero => rfl
    | succ k ih => rw [iter, ← ih]
  exact Computable.snd.comp (Computable.snd.comp hiter)

lemma primrec_allStr : Primrec allStr := by
  have hstep : Primrec₂ (fun (_ : ℕ) (l : List Str) =>
      l.flatMap (fun w => [false :: w, true :: w])) := by
    apply Primrec.list_flatMap Primrec.snd
    exact (Primrec.list_cons.comp
      (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
        (Primrec.const []))).to₂
  have := Primrec.nat_rec₁ (α := List Str) [([] : Str)] hstep
  refine this.of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [allStr, ← ih]

lemma primrec_allStrLe : Primrec allStrLe := by
  have hstep : Primrec₂ (fun (n : ℕ) (l : List Str) => l ++ allStr (n + 1)) :=
    Primrec.list_append.comp Primrec.snd
      (primrec_allStr.comp (Primrec.succ.comp Primrec.fst))
  have := Primrec.nat_rec₁ (α := List Str) [([] : Str)] hstep
  refine this.of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [allStrLe, ← ih]

instance : Countable (Machine α) := by
  classical
  have key : ∀ M : Machine α, ∃ c : Nat.Partrec.Code,
      ∀ a : α × Trans, c.eval (Encodable.encode a) = Part.some (Encodable.encode (M.step a)) := by
    intro M
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp M.hstep
    refine ⟨c, fun a => ?_⟩
    rw [hc]
    simp [Encodable.encodek]
  choose f hf using key
  refine Function.Injective.countable (f := f) ?_
  intro M₁ M₂ h
  have hstep : M₁.step = M₂.step := by
    funext a
    have h1 := hf M₁ a
    have h2 := hf M₂ a
    rw [h, h2] at h1
    exact Encodable.encode_injective (Part.some_injective h1.symm)
  obtain ⟨s1, p1⟩ := M₁
  obtain ⟨s2, p2⟩ := M₂
  cases hstep
  rfl

end Computability

/-! ## An oracle for which the classes coincide -/

/-- The empty oracle. -/
def emptyLang : Lang := fun _ => false

lemma computable_emptyLang : Computable emptyLang := Computable.const false

/-- A Boolean bounded existential over an initial segment of `ℕ`. -/
def existsUpto (p : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => p n || existsUpto p n

lemma existsUpto_eq_true {p : ℕ → Bool} {n : ℕ} :
    existsUpto p n = true ↔ ∃ i < n, p i = true := by
  induction n with
  | zero => simp [existsUpto]
  | succ n ih =>
      simp only [existsUpto, Bool.or_eq_true, ih]
      constructor
      · rintro (h | ⟨i, hi, hp⟩)
        · exact ⟨n, by omega, h⟩
        · exact ⟨i, by omega, hp⟩
      · rintro ⟨i, hi, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact Or.inr ⟨i, h, hp⟩
        · exact Or.inl hp

lemma existsUpto_list {l : List Str} {p : Str → Bool} :
    existsUpto (fun i => p (l[i]?.getD [])) l.length = true ↔ ∃ w ∈ l, p w = true := by
  rw [existsUpto_eq_true]
  constructor
  · rintro ⟨i, hi, hp⟩
    refine ⟨l[i]?.getD [], ?_, hp⟩
    rw [List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  · rintro ⟨w, hw, hp⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    exact ⟨i, hi, by simpa [List.getElem?_eq_getElem hi] using hp⟩

/-- A deterministic machine, viewed as a verifier which ignores its certificate. -/
def padMachine (M : Machine Str) : Machine (Str × Str) :=
  ⟨fun p => M.step (p.1.1, p.2),
    M.hstep.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)⟩

lemma iter_padMachine (M : Machine Str) (O : Lang) (x y : Str) (k : ℕ) :
    iter (padMachine M) O k ((x, y), [], none)
      = ((x, y), (iter M O k (x, [], none)).2.1, (iter M O k (x, [], none)).2.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iter, iter, ih]
      have hfst : (iter M O k (x, [], none)).1 = x := iter_fst M O _ k
      set t := iter M O k (x, [], none) with ht'
      rcases ht : t.2.2 with _ | b
      · rcases hs : M.step (x, t.2.1) with z | b <;>
          simp [next, padMachine, ht, hs, hfst]
      · simp [next, ht]

lemma run_padMachine (M : Machine Str) (O : Lang) (x y : Str) (k : ℕ) :
    run (padMachine M) O (x, y) k = run M O x k := by
  rw [run, run, iter_padMachine]

/-- The machine which immediately outputs `g x`, for a computable `g`. -/
def constMachine (g : Str → Bool) (hg : Computable g) : Machine Str :=
  ⟨fun p => Sum.inr (g p.1), Primrec.sumInr.to_comp.comp (hg.comp Computable.fst)⟩

lemma run_constMachine (g : Str → Bool) (hg : Computable g) (O : Lang) (x : Str) {k : ℕ}
    (hk : 1 ≤ k) : run (constMachine g hg) O x k = some (g x) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have key : ∀ j : ℕ, iter (constMachine g hg) O (j + 1) (x, [], none)
      = ((x, [], some (g x)) : Config Str) := by
    intro j
    induction j with
    | zero => simp [iter, next, constMachine]
    | succ j ih => rw [iter, ih, next_of_halted _ _ rfl]
  rw [run, key j]

lemma existsUpto_rec (p : ℕ → Bool) (n : ℕ) :
    Nat.rec (motive := fun _ => Bool) false (fun i ih => p i || ih) n = existsUpto p n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [existsUpto, ih]

/-- Brute-force decision of an `NP`-style acceptance condition: scan all
certificates of length at most the bound. -/
def npDecide (V : Machine (Str × Str)) (A : Lang) (c d : ℕ) (x : Str) : Bool :=
  existsUpto
    (fun i => (run V A (x, (allStrLe (polyBound c d x.length))[i]?.getD [])
      (polyBound c d x.length)).getD false)
    (allStrLe (polyBound c d x.length)).length

lemma npDecide_eq_true (V : Machine (Str × Str)) (A : Lang) (c d : ℕ) (x : Str) :
    npDecide V A c d x = true ↔ ∃ y : Str, y.length ≤ polyBound c d x.length ∧
      run V A (x, y) (polyBound c d x.length) = some true := by
  have h := existsUpto_list (l := allStrLe (polyBound c d x.length))
      (p := fun y => (run V A (x, y) (polyBound c d x.length)).getD false)
  refine h.trans ?_
  constructor
  · rintro ⟨w, hw, hpw⟩
    refine ⟨w, mem_allStrLe.mp hw, ?_⟩
    rcases hr : run V A (x, w) (polyBound c d x.length) with _ | b
    · rw [hr] at hpw; simp at hpw
    · cases b
      · rw [hr] at hpw; simp at hpw
      · rfl
  · rintro ⟨w, hw, hpw⟩
    exact ⟨w, mem_allStrLe.mpr hw, by rw [hpw]; rfl⟩

lemma computable_npDecide (V : Machine (Str × Str)) (A : Lang) (hA : Computable A) (c d : ℕ) :
    Computable (npDecide V A c d) := by
  have hm : Computable (fun x : Str => polyBound c d x.length) :=
    (Primrec.nat_mul.comp (Primrec.const c)
      ((Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.succ.comp Primrec.list_length)
        (Primrec.const d))).to_comp
  have hlist : Computable (fun x : Str => allStrLe (polyBound c d x.length)) :=
    primrec_allStrLe.to_comp.comp hm
  have hcert : Computable (fun q : Str × ℕ =>
      (allStrLe (polyBound c d q.1.length))[q.2]?.getD ([] : Str)) :=
    Computable.option_getD
      (Computable.list_getElem?.comp (hlist.comp Computable.fst) Computable.snd)
      (Computable.const [])
  have hP : Computable₂ (fun (x : Str) (i : ℕ) =>
      (run V A (x, (allStrLe (polyBound c d x.length))[i]?.getD [])
        (polyBound c d x.length)).getD false) :=
    Computable.option_getD
      ((computable_run V A hA).comp (Computable.pair Computable.fst hcert)
        (hm.comp Computable.fst))
      (Computable.const false)
  have hrec := Computable.nat_rec
    (f := fun x : Str => (allStrLe (polyBound c d x.length)).length)
    (g := fun _ : Str => false)
    (h := fun (x : Str) (q : ℕ × Bool) =>
      (run V A (x, (allStrLe (polyBound c d x.length))[q.1]?.getD [])
        (polyBound c d x.length)).getD false || q.2)
    (Computable.list_length.comp hlist) (Computable.const false)
    ((Primrec.dom_bool₂ (fun a b : Bool => a || b)).to_comp.comp
      (hP.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))
  refine hrec.of_eq fun x => ?_
  exact existsUpto_rec (fun i => (run V A (x, (allStrLe (polyBound c d x.length))[i]?.getD [])
    (polyBound c d x.length)).getD false) _

theorem collapse : PClass emptyLang = NPClass emptyLang := by
  apply Set.eq_of_subset_of_subset
  · rintro L ⟨M, c, d, hM⟩
    refine ⟨padMachine M, c, d, fun x => ?_⟩
    constructor
    · intro hx
      exact ⟨[], Nat.zero_le _, by rw [run_padMachine, hM x, hx]⟩
    · rintro ⟨y, -, hy⟩
      rw [run_padMachine, hM x] at hy
      exact Option.some_injective _ hy
  · rintro L ⟨V, c, d, hV⟩
    refine ⟨constMachine (npDecide V emptyLang c d)
      (computable_npDecide V emptyLang computable_emptyLang c d), c + 1, d, fun x => ?_⟩
    have hk : 1 ≤ polyBound (c + 1) d x.length := by
      have hpos : 0 < (x.length + 1) ^ d := by positivity
      simp only [polyBound]
      nlinarith
    rw [run_constMachine _ _ emptyLang x hk]
    have hequiv := (npDecide_eq_true V emptyLang c d x).trans (hV x).symm
    cases hn : npDecide V emptyLang c d x <;> cases hL : L x <;>
      simp [hn, hL] at hequiv ⊢

/-! ## An oracle separating the classes -/

/-- The test language: `x ∈ LB B` iff the oracle `B` contains some string of
length `|x|`. (Membership only depends on the length of `x`.) -/
def LB (B : Lang) : Lang := fun x => existsIn (allStr x.length) B

/-- The verifier for `LB B`: it checks that the certificate has the same length
as the input and then queries the oracle on it. -/
def lbVerifier : Machine (Str × Str) :=
  ⟨fun p =>
      match p.2 with
      | [] => if p.1.2.length = p.1.1.length then Sum.inl p.1.2 else Sum.inr false
      | (_, b) :: _ => Sum.inr b, by
    have hnil : Primrec (fun p : (Str × Str) × Trans =>
        if p.1.2.length = p.1.1.length then Sum.inl p.1.2 else (Sum.inr false : Str ⊕ Bool)) := by
      refine Primrec.ite ?_ (Primrec.sumInl.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.const (Sum.inr false))
      exact Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
    have hcons : Primrec₂ (fun (_ : (Str × Str) × Trans) (q : (Str × Bool) × Trans) =>
        (Sum.inr q.1.2 : Str ⊕ Bool)) :=
      Primrec.sumInr.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    refine (Primrec.list_casesOn Primrec.snd hnil hcons).to_comp.of_eq ?_
    rintro ⟨p, tr⟩
    cases tr <;> rfl⟩

lemma run_lbVerifier (B : Lang) (x y : Str) {k : ℕ} (hk : 2 ≤ k) :
    run lbVerifier B (x, y) k = some (if y.length = x.length then B y else false) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have key : ∀ j : ℕ, iter lbVerifier B (j + 2) ((x, y), [], none)
      = ((x, y), (if y.length = x.length then [(y, B y)] else []),
          some (if y.length = x.length then B y else false)) := by
    intro j
    induction j with
    | zero => by_cases h : y.length = x.length <;> simp [iter, next, lbVerifier, h]
    | succ j ih => rw [iter, ih, next_of_halted _ _ rfl]
  rw [run, key j]

theorem LB_mem_NP (B : Lang) : LB B ∈ NPClass B := by
  refine ⟨lbVerifier, 2, 1, fun x => ?_⟩
  have hpb : polyBound 2 1 x.length = 2 * (x.length + 1) := by simp [polyBound]
  have hbound : 2 ≤ polyBound 2 1 x.length := by omega
  constructor
  · intro hx
    obtain ⟨w, hw, hBw⟩ := existsIn_eq_true.mp hx
    have hlen : w.length = x.length := mem_allStr.mp hw
    refine ⟨w, by omega, ?_⟩
    rw [run_lbVerifier B x w hbound, if_pos hlen, hBw]
  · rintro ⟨y, -, hy⟩
    rw [run_lbVerifier B x y hbound] at hy
    by_cases h : y.length = x.length
    · rw [if_pos h] at hy
      refine existsIn_eq_true.mpr ⟨y, mem_allStr.mpr h, Option.some_injective _ hy⟩
    · rw [if_neg h] at hy
      simp at hy

/-- Polynomials are eventually dominated by `2^n`. -/
lemma poly_lt_two_pow (c d : ℕ) : ∃ N, ∀ n, N ≤ n → polyBound c d n < 2 ^ n := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (r := 2) (by norm_num)
  have hpos : (0:ℝ) < (c : ℝ) * 2 ^ d + 1 := by positivity
  have h2 := h.def (c := (1 : ℝ) / ((c : ℝ) * 2 ^ d + 1)) (by positivity)
  rw [Filter.eventually_atTop] at h2
  obtain ⟨N, hN⟩ := h2
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hNn : N ≤ n := le_trans (le_max_left N 1) hn
  have key := hN n hNn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at key
  have hcast : ((polyBound c d n : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
    push_cast [polyBound]
    have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have h1 : ((n : ℝ) + 1) ^ d ≤ (2 * (n:ℝ)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have h2 : (2 * (n:ℝ)) ^ d = 2 ^ d * (n:ℝ) ^ d := by rw [mul_pow]
    have h3 : (c:ℝ) * ((n:ℝ) + 1) ^ d ≤ (c:ℝ) * 2 ^ d * (n:ℝ)^d := by
      have hc : (0:ℝ) ≤ (c:ℝ) := by positivity
      nlinarith [h1, h2]
    have h4 : (c:ℝ) * 2 ^ d * (n:ℝ)^d ≤ (c:ℝ) * 2 ^ d * ((1 / ((c : ℝ) * 2 ^ d + 1)) * 2 ^ n) := by
      have : (0:ℝ) ≤ (c:ℝ) * 2 ^ d := by positivity
      nlinarith [key]
    have h5 : (c:ℝ) * 2 ^ d * ((1 / ((c : ℝ) * 2 ^ d + 1)) * 2 ^ n) < 2 ^ n := by
      have h2n : (0:ℝ) < 2 ^ n := by positivity
      have hlt : (c:ℝ) * 2 ^ d * (1 / ((c : ℝ) * 2 ^ d + 1)) < 1 := by
        rw [mul_one_div, div_lt_one hpos]
        linarith
      nlinarith
    linarith
  exact_mod_cast hcast

open Classical in
/-- A threshold beyond which the polynomial bound `c * (n+1)^d` is smaller than
the number `2^n` of strings of length `n`. -/
noncomputable def thr (c d : ℕ) : ℕ := (poly_lt_two_pow c d).choose

lemma thr_spec (c d : ℕ) : ∀ n, thr c d ≤ n → polyBound c d n < 2 ^ n :=
  (poly_lt_two_pow c d).choose_spec

section Separation

variable (E : ℕ → Machine Str × ℕ × ℕ)

/-- The indicator of a finite set of strings. -/
def orc (F : Finset Str) : Lang := fun w => decide (w ∈ F)

/-- The diagonalization length used at stage `i` when the frontier is `n`. -/
noncomputable def diagN (i n : ℕ) : ℕ := max n (thr (E i).2.1 (E i).2.2)

/-- The diagonalization input `1^N` used at stage `i`. -/
noncomputable def diagX (i n : ℕ) : Str := List.replicate (diagN E i n) true

/-- The step budget of the machine considered at stage `i`. -/
noncomputable def diagB (i n : ℕ) : ℕ := polyBound (E i).2.1 (E i).2.2 (diagN E i n)

/-- The queries made in the simulation at stage `i`. -/
noncomputable def diagQ (i n : ℕ) (F : Finset Str) : List Str :=
  queries (E i).1 (orc F) (diagX E i n) (diagB E i n)

/-- The verdict of the simulation at stage `i`. -/
noncomputable def diagR (i n : ℕ) (F : Finset Str) : Option Bool :=
  run (E i).1 (orc F) (diagX E i n) (diagB E i n)

/-- The maximal length of a list of strings. -/
def maxLen (Q : List Str) : ℕ := (Q.map List.length).foldr max 0

lemma le_maxLen {Q : List Str} {z : Str} (h : z ∈ Q) : z.length ≤ maxLen Q := by
  unfold maxLen
  induction Q with
  | nil => simp at h
  | cons a l ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · simp
      · simp only [List.map_cons, List.foldr_cons]
        exact le_trans (ih h') (le_max_right _ _)

/-- The new frontier after stage `i`: longer than the diagonalization length and
than every string queried during the simulation. -/
noncomputable def diagFront (i n : ℕ) (F : Finset Str) : ℕ :=
  max (diagN E i n + 1) (maxLen (diagQ E i n F) + 1)

open Classical in
/-- A string of length `N` avoiding `Q`, when one exists. -/
noncomputable def pick (N : ℕ) (Q : List Str) : Str :=
  if h : ∃ w : Str, w.length = N ∧ w ∉ Q then h.choose else []

lemma pick_spec {N : ℕ} {Q : List Str} (h : ∃ w : Str, w.length = N ∧ w ∉ Q) :
    (pick N Q).length = N ∧ pick N Q ∉ Q := by
  rw [pick, dif_pos h]
  exact h.choose_spec

/-- The stages of the construction: `(stage E i).1` is the frontier (all strings
of length `≥` it are still undecided) and `(stage E i).2` is the finite set of
strings put into the oracle so far. -/
noncomputable def stage : ℕ → ℕ × Finset Str
  | 0 => (0, ∅)
  | i + 1 =>
      if diagR E i (stage i).1 (stage i).2 = some true then
        (diagFront E i (stage i).1 (stage i).2, (stage i).2)
      else
        (diagFront E i (stage i).1 (stage i).2,
          insert (pick (diagN E i (stage i).1) (diagQ E i (stage i).1 (stage i).2)) (stage i).2)

open Classical in
/-- The oracle produced by the construction. -/
noncomputable def oracleB : Lang := fun w => decide (∃ i, w ∈ (stage E i).2)

lemma diag_exists_unqueried (i n : ℕ) (F : Finset Str) :
    ∃ w : Str, w.length = diagN E i n ∧ w ∉ diagQ E i n F := by
  refine exists_unqueried _ _ (lt_of_le_of_lt ?_ (thr_spec (E i).2.1 (E i).2.2 (diagN E i n)
    (le_max_right _ _)))
  exact queries_length_le _ _ _ _

lemma stage_succ_fst (i : ℕ) :
    (stage E (i + 1)).1 = diagFront E i (stage E i).1 (stage E i).2 := by
  rw [stage]; split <;> rfl

lemma stage_succ_of_true (i : ℕ)
    (h : diagR E i (stage E i).1 (stage E i).2 = some true) :
    (stage E (i + 1)).2 = (stage E i).2 := by
  rw [stage, if_pos h]

lemma stage_succ_of_false (i : ℕ)
    (h : ¬ diagR E i (stage E i).1 (stage E i).2 = some true) :
    (stage E (i + 1)).2 = insert (pick (diagN E i (stage E i).1)
      (diagQ E i (stage E i).1 (stage E i).2)) (stage E i).2 := by
  rw [stage, if_neg h]

lemma stage_succ_snd (i : ℕ) :
    (stage E (i + 1)).2 = (stage E i).2 ∨
      (stage E (i + 1)).2 = insert (pick (diagN E i (stage E i).1)
        (diagQ E i (stage E i).1 (stage E i).2)) (stage E i).2 := by
  by_cases h : diagR E i (stage E i).1 (stage E i).2 = some true
  · exact Or.inl (stage_succ_of_true E i h)
  · exact Or.inr (stage_succ_of_false E i h)

lemma stage_n_lt (i : ℕ) : (stage E i).1 < (stage E (i + 1)).1 := by
  have h1 : (stage E i).1 ≤ diagN E i (stage E i).1 := le_max_left _ _
  have h2 : diagN E i (stage E i).1 + 1 ≤ diagFront E i (stage E i).1 (stage E i).2 :=
    le_max_left _ _
  have h3 := stage_succ_fst E i
  omega

lemma stage_F_succ (i : ℕ) : (stage E i).2 ⊆ (stage E (i + 1)).2 := by
  rcases stage_succ_snd E i with h | h
  · rw [h]
  · rw [h]; exact Finset.subset_insert _ _

lemma stage_F_mono {i j : ℕ} (h : i ≤ j) : (stage E i).2 ⊆ (stage E j).2 := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @step j hij ih => exact ih.trans (stage_F_succ E j)

lemma stage_n_mono {i j : ℕ} (h : i ≤ j) : (stage E i).1 ≤ (stage E j).1 := by
  induction h with
  | refl => exact le_rfl
  | @step j hij ih => exact le_trans ih (le_of_lt (stage_n_lt E j))

lemma stage_len_lt (i : ℕ) : ∀ w ∈ (stage E i).2, w.length < (stage E i).1 := by
  induction i with
  | zero => intro w hw; simp [stage] at hw
  | succ i ih =>
      intro w hw
      have hlt := stage_n_lt E i
      by_cases hc : diagR E i (stage E i).1 (stage E i).2 = some true
      · rw [stage_succ_of_true E i hc] at hw
        have := ih w hw
        omega
      · rw [stage_succ_of_false E i hc] at hw
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · have hp := (pick_spec (diag_exists_unqueried E i (stage E i).1 (stage E i).2)).1
          have h2 : diagN E i (stage E i).1 + 1 ≤ diagFront E i (stage E i).1 (stage E i).2 :=
            le_max_left _ _
          have h3 := stage_succ_fst E i
          omega
        · have := ih w hw'
          omega

lemma stage_new_long (i : ℕ) : ∀ w ∈ (stage E (i + 1)).2, w ∉ (stage E i).2 →
    (stage E i).1 ≤ w.length := by
  intro w hw hnw
  rcases stage_succ_snd E i with h | h
  · rw [h] at hw; exact absurd hw hnw
  · rw [h] at hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · rw [(pick_spec (diag_exists_unqueried E i (stage E i).1 (stage E i).2)).1]
      exact le_max_left _ _
    · exact absurd hw' hnw

lemma stage_stable {i j : ℕ} (hij : i ≤ j) {w : Str} (hw : w ∈ (stage E j).2)
    (hlen : w.length < (stage E i).1) : w ∈ (stage E i).2 := by
  induction hij with
  | refl => exact hw
  | @step j hij ih =>
      refine ih ?_
      by_cases hmem : w ∈ (stage E j).2
      · exact hmem
      · exfalso
        have h1 := stage_new_long E j w hw hmem
        have h2 := stage_n_mono E hij
        omega

lemma oracleB_eq (i : ℕ) {w : Str} (hlen : w.length < (stage E i).1) :
    oracleB E w = decide (w ∈ (stage E i).2) := by
  have hiff : (∃ j, w ∈ (stage E j).2) ↔ w ∈ (stage E i).2 := by
    constructor
    · rintro ⟨j, hj⟩
      rcases le_total i j with h | h
      · exact stage_stable E h hj hlen
      · exact stage_F_mono E h hj
    · exact fun h => ⟨i, h⟩
  simp only [oracleB]
  exact decide_eq_decide.mpr hiff

theorem LB_not_mem_P (hE : Function.Surjective E) :
    LB (oracleB E) ∉ PClass (oracleB E) := by
  rintro ⟨M, c, d, hM⟩
  obtain ⟨i, hi⟩ := hE (M, c, d)
  have hM1 : (E i).1 = M := by rw [hi]
  have hc : (E i).2.1 = c := by rw [hi]
  have hd : (E i).2.2 = d := by rw [hi]
  set n := (stage E i).1 with hn
  set F := (stage E i).2 with hF
  set N := diagN E i n with hN
  set Q := diagQ E i n F with hQ
  have hxlen : (diagX E i n).length = N := by rw [diagX]; simp [hN]
  have hbud : polyBound c d (diagX E i n).length = diagB E i n := by
    rw [hxlen, diagB, hc, hd, ← hN]
  have hfront : (stage E (i + 1)).1 = diagFront E i n F := stage_succ_fst E i
  have hNlt : N < (stage E (i + 1)).1 := by
    have h2 : N + 1 ≤ diagFront E i n F := le_max_left _ _
    omega
  have hQlt : ∀ z ∈ Q, z.length < (stage E (i + 1)).1 := by
    intro z hz
    have h1 := le_maxLen hz
    have h2 : maxLen Q + 1 ≤ diagFront E i n F := le_max_right _ _
    omega
  have hmemiff : ∀ z ∈ Q, (z ∈ (stage E (i + 1)).2 ↔ z ∈ F) := by
    intro z hz
    rcases stage_succ_snd E i with h | h
    · rw [h]
    · rw [h, Finset.mem_insert]
      constructor
      · rintro (rfl | hzF)
        · exact absurd hz (pick_spec (diag_exists_unqueried E i n F)).2
        · exact hzF
      · exact fun h => Or.inr h
  have hagree : ∀ z ∈ queries (E i).1 (orc F) (diagX E i n) (diagB E i n),
      orc F z = oracleB E z := by
    intro z hz
    have hz' : z ∈ Q := hz
    rw [oracleB_eq E (i + 1) (hQlt z hz')]
    exact decide_eq_decide.mpr (hmemiff z hz').symm
  have hrun : run (E i).1 (oracleB E) (diagX E i n) (diagB E i n) = diagR E i n F :=
    run_congr _ _ _ _ _ hagree
  have hMrun : diagR E i n F = some (LB (oracleB E) (diagX E i n)) := by
    have h := hM (diagX E i n)
    rw [hbud, ← hM1] at h
    rw [← hrun]
    exact h
  by_cases hcase : diagR E i n F = some true
  · have hLB : LB (oracleB E) (diagX E i n) ≠ true := by
      intro hLBt
      obtain ⟨w, hw, hBw⟩ := existsIn_eq_true.mp hLBt
      have hwlen : w.length = N := by rw [mem_allStr.mp hw, hxlen]
      have hwlt : w.length < (stage E (i + 1)).1 := by omega
      have heq : oracleB E w = decide (w ∈ (stage E (i + 1)).2) := oracleB_eq E (i + 1) hwlt
      rw [hBw] at heq
      have hmem : w ∈ (stage E (i + 1)).2 := by
        by_contra hc'
        simp [hc'] at heq
      rw [stage_succ_of_true E i hcase] at hmem
      have h1 := stage_len_lt E i w hmem
      have h2 : n ≤ N := le_max_left _ _
      omega
    rw [hcase] at hMrun
    exact hLB (Option.some_injective _ hMrun).symm
  · have hp := pick_spec (diag_exists_unqueried E i n F)
    have hpmem : pick N Q ∈ (stage E (i + 1)).2 := by
      rw [stage_succ_of_false E i hcase]
      exact Finset.mem_insert_self _ _
    have hpB : oracleB E (pick N Q) = true := by
      have hex : ∃ j, pick N Q ∈ (stage E j).2 := ⟨i + 1, hpmem⟩
      simpa [oracleB] using hex
    have hLB : LB (oracleB E) (diagX E i n) = true := by
      refine existsIn_eq_true.mpr ⟨pick N Q, ?_, hpB⟩
      rw [mem_allStr, hxlen]
      exact hp.1
    rw [hLB] at hMrun
    exact hcase hMrun

end Separation

instance : Nonempty (Machine Str) := ⟨constMachine (fun _ => false) (Computable.const false)⟩

theorem separation : ∃ B : Lang, PClass B ≠ NPClass B := by
  obtain ⟨E, hE⟩ := exists_surjective_nat (Machine Str × ℕ × ℕ)
  refine ⟨oracleB E, fun h => ?_⟩
  have h1 : LB (oracleB E) ∈ NPClass (oracleB E) := LB_mem_NP _
  rw [← h] at h1
  exact LB_not_mem_P E hE h1

/-- **Baker–Gill–Solovay**: there is an oracle relative to which `P = NP` and an
oracle relative to which `P ≠ NP`. -/
theorem baker_gill_solovay :
    (∃ A : Lang, PClass A = NPClass A) ∧ (∃ B : Lang, PClass B ≠ NPClass B) :=
  ⟨⟨emptyLang, collapse⟩, separation⟩

end CS

