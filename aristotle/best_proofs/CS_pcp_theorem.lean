/-
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-! ## Words, languages, proofs -/

/-- A binary word. -/
abbrev Word := List Bool

/-- A language: a set of binary words. -/
abbrev Lang := Word → Prop

/-- A PCP proof (proof oracle): an infinite binary string. -/
abbrev Assignment := ℕ → Bool

/-! ## Local tests (constraints)

A non-adaptive PCP verifier, on a fixed input `x` and a fixed random string, reads a fixed
tuple of positions of the proof oracle and applies a predicate to the bits it read.  Such a
single action is exactly a *constraint*.
-/

/-- A single local test: a list of queried proof positions together with a predicate on the
answers. -/
structure Constraint where
  /-- The positions of the proof oracle that are queried. -/
  vars : List ℕ
  /-- The acceptance predicate applied to the answers, in the order of `vars`. -/
  pred : List Bool → Bool

/-- The number of queries made by a test. -/
def Constraint.arity (c : Constraint) : ℕ := c.vars.length

/-- Whether a test accepts a given proof oracle. -/
def Constraint.sat (c : Constraint) (a : Assignment) : Bool := c.pred (c.vars.map a)

/-- The conjunction of two tests: query both tuples, accept iff both tests accept. -/
def Constraint.conj (c d : Constraint) : Constraint where
  vars := c.vars ++ d.vars
  pred := fun bs => c.pred (bs.take c.vars.length) && d.pred (bs.drop c.vars.length)

@[simp] theorem Constraint.sat_conj (c d : Constraint) (a : Assignment) :
    (c.conj d).sat a = (c.sat a && d.sat a) := by
  simp [Constraint.conj, Constraint.sat, List.map_append,
    List.take_left', List.drop_left']

/-- The trivial test: no queries, always accepts. -/
def Constraint.triv : Constraint where
  vars := []
  pred := fun _ => true

@[simp] theorem Constraint.sat_triv (a : Assignment) : Constraint.triv.sat a = true := rfl

/-! ## Test systems

Fixing the input `x`, a non-adaptive PCP verifier that tosses `r` coins is described by the
list of the `2 ^ r` tests it may perform, one for each random string; it picks one of them
uniformly at random.  Thus the number of random bits is `log₂` of the number of tests, and
"`O(log n)` random bits" is the same as "polynomially many tests".
-/

/-- A test system: a nonempty list of local tests, one per random string. -/
structure TestSystem where
  /-- The list of tests, indexed by the random string. -/
  tests : List Constraint
  /-- There is at least one test. -/
  tests_ne : tests ≠ []

/-- The probability that the verifier accepts the proof `a`, i.e. the fraction of tests of the
system that accept `a`. -/
noncomputable def acceptProb (T : TestSystem) (a : Assignment) : ℚ :=
  (T.tests.countP (fun c => c.sat a) : ℚ) / (T.tests.length : ℚ)

theorem TestSystem.length_pos (T : TestSystem) : 0 < T.tests.length :=
  List.length_pos_iff.mpr T.tests_ne

theorem acceptProb_nonneg (T : TestSystem) (a : Assignment) : 0 ≤ acceptProb T a := by
  apply div_nonneg <;> positivity

theorem acceptProb_le_one (T : TestSystem) (a : Assignment) : acceptProb T a ≤ 1 := by
  rw [acceptProb, div_le_one (by exact_mod_cast T.length_pos)]
  exact_mod_cast List.countP_le_length

theorem acceptProb_eq_one_iff (T : TestSystem) (a : Assignment) :
    acceptProb T a = 1 ↔ ∀ c ∈ T.tests, c.sat a = true := by
  have hlen : (0 : ℚ) < (T.tests.length : ℚ) := by exact_mod_cast T.length_pos
  rw [acceptProb, div_eq_one_iff_eq (ne_of_gt hlen)]
  constructor
  · intro h
    have : T.tests.countP (fun c => c.sat a) = T.tests.length := by exact_mod_cast h
    have := (List.countP_eq_length (l := T.tests) (p := fun c => c.sat a)).mp this
    simpa using this
  · intro h
    have : T.tests.countP (fun c => c.sat a) = T.tests.length :=
      (List.countP_eq_length (l := T.tests) (p := fun c => c.sat a)).mpr (by simpa using h)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) this

/-! ## Sequential repetition of a test system -/

/-- Independent `n`-fold repetition of a test system: perform `n` independent runs of the
verifier and accept iff all of them accept. -/
def TestSystem.pow (T : TestSystem) : ℕ → TestSystem
  | 0 => ⟨[Constraint.triv], by simp⟩
  | (n + 1) =>
      ⟨T.tests.flatMap (fun c => (T.pow n).tests.map (fun d => c.conj d)), by
        intro h
        have h1 := T.tests_ne
        have h2 := (T.pow n).tests_ne
        rcases List.exists_mem_of_ne_nil _ h1 with ⟨c, hc⟩
        rcases List.exists_mem_of_ne_nil _ h2 with ⟨d, hd⟩
        have : c.conj d ∈ T.tests.flatMap (fun c => (T.pow n).tests.map (fun d => c.conj d)) := by
          rw [List.mem_flatMap]
          exact ⟨c, hc, List.mem_map_of_mem hd⟩
        rw [h] at this
        simp at this⟩

theorem countP_flatMap_conj (L M : List Constraint) (a : Assignment) :
    (L.flatMap (fun c => M.map (fun d => c.conj d))).countP (fun c => c.sat a)
      = (L.countP (fun c => c.sat a)) * (M.countP (fun c => c.sat a)) := by
  induction L with
  | nil => simp
  | cons c L ih =>
      rw [List.flatMap_cons, List.countP_append, ih, List.countP_map]
      by_cases hc : c.sat a = true
      · have : (fun c' => Constraint.sat c' a) ∘ (fun d => c.conj d)
            = fun d => d.sat a := by
          funext d; simp [hc]
        rw [this, List.countP_cons_of_pos (by simpa using hc)]
        ring
      · have hc' : c.sat a = false := by simpa using hc
        have : (fun c' => Constraint.sat c' a) ∘ (fun d => c.conj d)
            = fun _ => false := by
          funext d; simp [hc']
        rw [this, List.countP_cons_of_neg (by simp [hc'])]
        simp

theorem TestSystem.length_pow (T : TestSystem) (n : ℕ) :
    (T.pow n).tests.length = T.tests.length ^ n := by
  induction n with
  | zero => simp [TestSystem.pow]
  | succ n ih =>
      show (T.tests.flatMap (fun c => (T.pow n).tests.map (fun d => c.conj d))).length = _
      rw [List.length_flatMap]
      simp only [List.length_map, ih, List.map_const', List.sum_replicate, smul_eq_mul]
      rw [pow_succ]
      ring

theorem TestSystem.countP_pow (T : TestSystem) (n : ℕ) (a : Assignment) :
    (T.pow n).tests.countP (fun c => c.sat a)
      = (T.tests.countP (fun c => c.sat a)) ^ n := by
  induction n with
  | zero => simp [TestSystem.pow]
  | succ n ih =>
      show ((T.tests.flatMap (fun c => (T.pow n).tests.map (fun d => c.conj d))).countP
        (fun c => c.sat a)) = _
      rw [countP_flatMap_conj, ih, pow_succ, mul_comm]

theorem acceptProb_pow (T : TestSystem) (n : ℕ) (a : Assignment) :
    acceptProb (T.pow n) a = (acceptProb T a) ^ n := by
  rw [acceptProb, acceptProb, T.countP_pow n a, T.length_pow n, div_pow]
  push_cast
  ring

/-! ## Bounds preserved by repetition -/

theorem TestSystem.pow_arity_le (T : TestSystem) (q n : ℕ)
    (h : ∀ c ∈ T.tests, c.arity ≤ q) :
    ∀ c ∈ (T.pow n).tests, c.arity ≤ q * n := by
  induction n with
  | zero => intro c hc; simp [TestSystem.pow] at hc; simp [hc, Constraint.arity, Constraint.triv]
  | succ n ih =>
      intro c hc
      have hc' : c ∈ T.tests.flatMap (fun c => (T.pow n).tests.map (fun d => c.conj d)) := hc
      rw [List.mem_flatMap] at hc'
      obtain ⟨d, hd, hmem⟩ := hc'
      rw [List.mem_map] at hmem
      obtain ⟨e, he, rfl⟩ := hmem
      have h1 := h d hd
      have h2 := ih e he
      simp only [Constraint.arity, Constraint.conj, List.length_append] at *
      calc d.vars.length + e.vars.length ≤ q + q * n := Nat.add_le_add h1 h2
        _ = q * (n + 1) := by ring

theorem TestSystem.pow_vars_mem (T : TestSystem) (n : ℕ) :
    ∀ c ∈ (T.pow n).tests, ∀ i ∈ c.vars, ∃ d ∈ T.tests, i ∈ d.vars := by
  induction n with
  | zero =>
      intro c hc i hi
      simp [TestSystem.pow] at hc
      subst hc
      simp [Constraint.triv] at hi
  | succ n ih =>
      intro c hc i hi
      have hc' : c ∈ T.tests.flatMap (fun c => (T.pow n).tests.map (fun d => c.conj d)) := hc
      rw [List.mem_flatMap] at hc'
      obtain ⟨d, hd, hmem⟩ := hc'
      rw [List.mem_map] at hmem
      obtain ⟨e, he, rfl⟩ := hmem
      simp only [Constraint.conj, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ⟨d, hd, hi⟩
      · exact ih e he i hi

/-! ## An abstract model of polynomial-time computation

Formalizing polynomial-time computability from scratch requires fixing a machine model.  We
instead work with an *abstract* model: a class `Ver` of polynomial-time computable verification
predicates and a class `Sys` of polynomial-time computable maps from inputs to test systems
(the tests being represented by their query tuples together with the truth tables of their
predicates), subject to the two closure properties that the arguments below need.  Both are
true of the standard notion of polynomial time, and everything is a hypothesis of the final
theorem: no new Lean axiom is introduced.
-/

/-- An abstract model of efficient (polynomial-time) computation. -/
structure EffModel where
  /-- `Ver V` says that the two-argument predicate `V` is polynomial-time computable. -/
  Ver : (Word → Word → Bool) → Prop
  /-- `Sys V` says that the map from an input to a test system is polynomial-time computable
  (tests being given by their query tuples and the truth tables of their predicates). -/
  Sys : (Word → TestSystem) → Prop
  /-- Given an efficiently computable test system, checking that *all* of its tests accept a
  candidate proof is a polynomial-time verification predicate. -/
  ver_all : ∀ {V : Word → TestSystem}, Sys V →
    Ver (fun x w => (V x).tests.all (fun c => c.sat (fun i => w.getD i false)))
  /-- For each fixed number `t` of repetitions, the `t`-fold repetition of an efficiently
  computable test system is efficiently computable. -/
  sys_pow : ∀ {V : Word → TestSystem} (t : ℕ), Sys V → Sys (fun x => (V x).pow t)
  /-- `Red f` says that the word function `f` is polynomial-time computable. -/
  Red : (Word → Word) → Prop
  /-- Efficient maps compose: precomposing an efficient test system with an efficient word
  function is efficient. -/
  sys_comp : ∀ {V : Word → TestSystem} {f : Word → Word}, Sys V → Red f →
    Sys (fun x => V (f x))
  /-- A polynomial-time computable word function has polynomially bounded output length. -/
  red_poly : ∀ {f : Word → Word}, Red f → ∃ k : ℕ, ∀ x : Word,
    (f x).length ≤ (x.length + 2) ^ k

/-! ## The classes NP and PCP(log n, 1) -/

/-- `NP`: languages with polynomial-length certificates checkable in polynomial time. -/
def NPclass (M : EffModel) : Set Lang :=
  {L | ∃ (V : Word → Word → Bool) (c : ℕ), M.Ver V ∧
        ∀ x : Word, L x ↔ ∃ w : Word, w.length ≤ (x.length + 2) ^ c ∧ V x w = true}

/-- `PCP(log n, 1)`: languages having a probabilistically checkable proof system with
`O(log n)` random bits (equivalently, polynomially many possible tests), `O(1)` queries,
polynomially long proofs, perfect completeness and soundness error at most `1/2`. -/
def PCPclass (M : EffModel) : Set Lang :=
  {L | ∃ (V : Word → TestSystem) (q c : ℕ), M.Sys V ∧
        (∀ x : Word, ∀ t ∈ (V x).tests, t.arity ≤ q) ∧
        (∀ x : Word, (V x).tests.length ≤ (x.length + 2) ^ c) ∧
        (∀ x : Word, ∀ t ∈ (V x).tests, ∀ i ∈ t.vars, i < (x.length + 2) ^ c) ∧
        (∀ x : Word, L x → ∃ a : Assignment, acceptProb (V x) a = 1) ∧
        (∀ x : Word, ¬ L x → ∀ a : Assignment, acceptProb (V x) a ≤ 1 / 2)}

/-! ## The combinatorial core of the PCP theorem

The deep content of the PCP theorem (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy; Dinur's
proof) is the existence of *constant-gap* probabilistically checkable proofs for NP: every NP
language admits an efficient reduction to a system of `O(1)`-query local tests such that YES
instances are perfectly satisfiable while for NO instances every proof fails a constant
fraction of the tests.  This is stated here as a hypothesis; it is not proved in this
development.  What *is* proved below is that this hypothesis is equivalent to the equality
`NP = PCP(log n, 1)`: the soundness amplification from a constant gap to `1/2`, and the
converse inclusion `PCP(log n, 1) ⊆ NP`, are established unconditionally.  It is further
shown (`pcp_theorem_of_gap_npHard`) that it suffices to assume the constant gap for a single
NP-hard language, since constant-gap PCPs transfer along polynomial-time reductions.
-/

/-- `GapVerifier M L`: the language `L` has an efficient `O(1)`-query PCP verifier with
perfect completeness and a *constant* soundness gap `eps > 0`. -/
def GapVerifier (M : EffModel) (L : Lang) : Prop :=
  ∃ (V : Word → TestSystem) (q c : ℕ) (eps : ℚ),
        0 < eps ∧ eps ≤ 1 ∧ M.Sys V ∧
        (∀ x : Word, ∀ t ∈ (V x).tests, t.arity ≤ q) ∧
        (∀ x : Word, (V x).tests.length ≤ (x.length + 2) ^ c) ∧
        (∀ x : Word, ∀ t ∈ (V x).tests, ∀ i ∈ t.vars, i < (x.length + 2) ^ c) ∧
        (∀ x : Word, L x → ∃ a : Assignment, acceptProb (V x) a = 1) ∧
        (∀ x : Word, ¬ L x → ∀ a : Assignment, acceptProb (V x) a ≤ 1 - eps)

/-- Constant-gap PCPs for NP: the combinatorial core of the PCP theorem. -/
def GapPCP (M : EffModel) : Prop := ∀ L ∈ NPclass M, GapVerifier M L

/-! ## The easy inclusion: `PCP(log n, 1) ⊆ NP` -/

theorem PCP_subset_NP (M : EffModel) : PCPclass M ⊆ NPclass M := by
  rintro L ⟨V, q, c, hSys, _hq, _hlen, hvars, hcomp, hsound⟩
  refine ⟨fun x w => (V x).tests.all (fun t => t.sat (fun i => w.getD i false)), c,
    M.ver_all hSys, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := hcomp x hx
    refine ⟨(List.range ((x.length + 2) ^ c)).map a, by simp, ?_⟩
    have hall := (acceptProb_eq_one_iff (V x) a).mp ha
    simp only [List.all_eq_true]
    intro t ht
    have hgetD : ∀ i ∈ t.vars,
        ((List.range ((x.length + 2) ^ c)).map a).getD i false = a i := by
      intro i hi
      have hlt : i < (x.length + 2) ^ c := hvars x t ht i hi
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_map, List.getElem?_range hlt]
      rfl
    have h2 := hall t ht
    rw [Constraint.sat, List.map_congr_left hgetD]
    exact h2
  · rintro ⟨w, _hw, hV⟩
    by_contra hx
    have hall : ∀ t ∈ (V x).tests, t.sat (fun i => w.getD i false) = true := by
      simpa using hV
    have h1 : acceptProb (V x) (fun i => w.getD i false) = 1 :=
      (acceptProb_eq_one_iff (V x) _).mpr hall
    have h2 := hsound x hx (fun i => w.getD i false)
    rw [h1] at h2
    norm_num at h2

/-! ## Soundness amplification and the hard inclusion -/

/-- If `0 ≤ p ≤ 1 - eps` with `0 < eps ≤ 1`, then `p ^ t ≤ 1 / 2` for a suitable constant
number `t ≥ 1` of repetitions, uniformly in `p`. -/
theorem exists_repetitions (eps : ℚ) (heps : 0 < eps) :
    ∃ t : ℕ, 1 ≤ t ∧ ∀ p : ℚ, 0 ≤ p → p ≤ 1 - eps → p ^ t ≤ 1 / 2 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := (1 : ℚ) / 2) (y := 1 - eps)
    (by norm_num) (by linarith)
  refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
  intro p hp hple
  have h0 : (0 : ℚ) ≤ 1 - eps := le_trans hp hple
  have hmono : p ^ (n + 1) ≤ (1 - eps) ^ (n + 1) := pow_le_pow_left₀ hp hple _
  have hshrink : (1 - eps) ^ (n + 1) ≤ (1 - eps) ^ n :=
    pow_le_pow_of_le_one h0 (by linarith) (Nat.le_succ n)
  linarith [hmono, hshrink, hn.le]

theorem NP_subset_PCP (M : EffModel) (h : GapPCP M) : NPclass M ⊆ PCPclass M := by
  intro L hL
  obtain ⟨V, q, c, eps, heps, heps1, hSys, hq, hlen, hvars, hcomp, hsound⟩ := h L hL
  obtain ⟨t, ht1, ht⟩ := exists_repetitions eps heps
  refine ⟨fun x => (V x).pow t, q * t, c * t, M.sys_pow t hSys, ?_, ?_, ?_, ?_, ?_⟩
  · intro x s hs
    exact (V x).pow_arity_le q t (hq x) s hs
  · intro x
    rw [TestSystem.length_pow, pow_mul]
    exact Nat.pow_le_pow_left (hlen x) t
  · intro x s hs i hi
    obtain ⟨d, hd, hid⟩ := (V x).pow_vars_mem t s hs i hi
    have h1 : i < (x.length + 2) ^ c := hvars x d hd i hid
    have h2 : (x.length + 2) ^ c ≤ (x.length + 2) ^ (c * t) := by
      apply Nat.pow_le_pow_right (by omega)
      exact Nat.le_mul_of_pos_right c (by omega)
    omega
  · intro x hx
    obtain ⟨a, ha⟩ := hcomp x hx
    exact ⟨a, by rw [acceptProb_pow, ha, one_pow]⟩
  · intro x hx a
    rw [acceptProb_pow]
    exact ht _ (acceptProb_nonneg _ _) (hsound x hx a)

/-! ## The PCP theorem -/

/-- **The PCP theorem**, `NP = PCP(log n, 1)`.

Languages in `NP` are exactly the languages having a probabilistically checkable proof system
that uses `O(log n)` random bits (i.e. polynomially many possible local tests), reads `O(1)`
bits of a polynomially long proof, always accepts a correct proof for a member of the
language, and accepts any purported proof for a non-member with probability at most `1/2`.

The statement is relative to an abstract axiomatization `M` of polynomial-time computation,
and is conditional on `GapPCP M`, the combinatorial core of the PCP theorem (existence of
constant-gap PCPs for NP), which is assumed rather than proved here.  The two inclusions —
soundness amplification of the constant gap to `1/2` for the hard direction, and the
enumeration of all random strings for the easy direction `PCP(log n, 1) ⊆ NP` — are proved. -/
theorem pcp_theorem (M : EffModel) (h : GapPCP M) : NPclass M = PCPclass M :=
  Set.Subset.antisymm (NP_subset_PCP M h) (PCP_subset_NP M)

/-- Conversely, the PCP theorem implies constant-gap PCPs for NP (with gap `1/2`). -/
theorem gapPCP_of_pcp (M : EffModel) (h : NPclass M = PCPclass M) : GapPCP M := by
  intro L hL
  obtain ⟨V, q, c, hSys, hq, hlen, hvars, hcomp, hsound⟩ := h ▸ hL
  refine ⟨V, q, c, 1 / 2, by norm_num, by norm_num, hSys, hq, hlen, hvars, hcomp, ?_⟩
  intro x hx a
  have := hsound x hx a
  linarith

/-- The PCP theorem `NP = PCP(log n, 1)` is *equivalent* to its combinatorial core, the
existence of constant-gap probabilistically checkable proofs for NP.  This equivalence is
unconditional. -/
theorem pcp_theorem_iff_gapPCP (M : EffModel) : NPclass M = PCPclass M ↔ GapPCP M :=
  ⟨gapPCP_of_pcp M, pcp_theorem M⟩

/-! ## Reducing the assumption to a single NP-hard language

The core hypothesis need only be assumed for *one* NP-hard language: constant-gap PCPs then
transfer along polynomial-time many-one reductions, which is what the standard statement of
the PCP theorem (NP-hardness of gap constraint satisfaction) provides. -/

/-- Polynomial-time many-one reducibility. -/
def Reduces (M : EffModel) (L K : Lang) : Prop :=
  ∃ f : Word → Word, M.Red f ∧ ∀ x : Word, L x ↔ K (f x)

/-- `K` is NP-hard under polynomial-time many-one reductions. -/
def NPHard (M : EffModel) (K : Lang) : Prop := ∀ L ∈ NPclass M, Reduces M L K

/-- Composing polynomial bounds: `((n + 2) ^ k + 2) ^ c ≤ (n + 2) ^ ((k + 2) * c)`. -/
theorem poly_comp_bound (n k c : ℕ) : ((n + 2) ^ k + 2) ^ c ≤ (n + 2) ^ ((k + 2) * c) := by
  have h1 : 1 ≤ (n + 2) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : (n + 2) ^ k + 2 ≤ (n + 2) ^ (k + 2) := by
    have : (n + 2) ^ (k + 2) = (n + 2) ^ k * ((n + 2) * (n + 2)) := by ring
    have h4 : 4 * (n + 2) ^ k ≤ (n + 2) ^ k * ((n + 2) * (n + 2)) := by
      have : 4 ≤ (n + 2) * (n + 2) := by nlinarith
      calc 4 * (n + 2) ^ k ≤ ((n + 2) * (n + 2)) * (n + 2) ^ k := Nat.mul_le_mul_right _ this
        _ = (n + 2) ^ k * ((n + 2) * (n + 2)) := by ring
    omega
  calc ((n + 2) ^ k + 2) ^ c ≤ ((n + 2) ^ (k + 2)) ^ c := Nat.pow_le_pow_left h2 c
    _ = (n + 2) ^ ((k + 2) * c) := by rw [← pow_mul]

/-- Constant-gap PCPs transfer along polynomial-time many-one reductions. -/
theorem gapVerifier_of_reduces (M : EffModel) (L K : Lang) (hred : Reduces M L K)
    (hK : GapVerifier M K) : GapVerifier M L := by
  obtain ⟨f, hf, hfL⟩ := hred
  obtain ⟨k, hk⟩ := M.red_poly hf
  obtain ⟨V, q, c, eps, heps, heps1, hSys, hq, hlen, hvars, hcomp, hsound⟩ := hK
  refine ⟨fun x => V (f x), q, (k + 2) * c, eps, heps, heps1, M.sys_comp hSys hf, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x t ht; exact hq (f x) t ht
  · intro x
    calc (V (f x)).tests.length ≤ ((f x).length + 2) ^ c := hlen (f x)
      _ ≤ ((x.length + 2) ^ k + 2) ^ c := Nat.pow_le_pow_left (by have := hk x; omega) c
      _ ≤ (x.length + 2) ^ ((k + 2) * c) := poly_comp_bound _ _ _
  · intro x t ht i hi
    have h1 : i < ((f x).length + 2) ^ c := hvars (f x) t ht i hi
    have h2 : ((f x).length + 2) ^ c ≤ ((x.length + 2) ^ k + 2) ^ c :=
      Nat.pow_le_pow_left (by have := hk x; omega) c
    have h3 := poly_comp_bound x.length k c
    omega
  · intro x hx; exact hcomp (f x) ((hfL x).mp hx)
  · intro x hx a; exact hsound (f x) (fun h => hx ((hfL x).mpr h)) a

/-- A constant-gap PCP for a single NP-hard language gives constant-gap PCPs for all of NP. -/
theorem gapPCP_of_npHard (M : EffModel) (K : Lang) (hhard : NPHard M K)
    (hK : GapVerifier M K) : GapPCP M :=
  fun L hL => gapVerifier_of_reduces M L K (hhard L hL) hK

/-- **The PCP theorem from gap hardness.**  If some NP-hard language admits an efficient
`O(1)`-query PCP with perfect completeness and a constant soundness gap, then
`NP = PCP(log n, 1)`. -/
theorem pcp_theorem_of_gap_npHard (M : EffModel) (K : Lang) (hhard : NPHard M K)
    (hK : GapVerifier M K) : NPclass M = PCPclass M :=
  pcp_theorem M (gapPCP_of_npHard M K hhard hK)

/-! ## Non-vacuity

The hypotheses above are satisfiable: there is an `EffModel` satisfying `GapPCP` (take the
degenerate model in which every function counts as efficient).  Hence `pcp_theorem` is not
vacuously true. -/

/-- The degenerate model in which every function is deemed efficiently computable (word
functions being additionally required to have polynomially bounded output length). -/
def trivialModel : EffModel where
  Ver := fun _ => True
  Sys := fun _ => True
  ver_all := fun _ => trivial
  sys_pow := fun _ _ => trivial
  Red := fun f => ∃ k : ℕ, ∀ x : Word, (f x).length ≤ (x.length + 2) ^ k
  sys_comp := fun _ _ => trivial
  red_poly := fun h => h

/-- The always-rejecting test, making no queries. -/
def Constraint.reject : Constraint where
  vars := []
  pred := fun _ => false

theorem gapVerifier_trivialModel (L : Lang) : GapVerifier trivialModel L := by
  classical
  refine ⟨fun x => if L x then ⟨[Constraint.triv], by simp⟩ else ⟨[Constraint.reject], by simp⟩,
    0, 0, 1 / 2, by norm_num, by norm_num, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · intro x t ht
    by_cases hx : L x <;> simp [hx, Constraint.arity, Constraint.triv, Constraint.reject] at ht ⊢
      <;> simp [ht]
  · intro x; by_cases hx : L x <;> simp [hx]
  · intro x t ht i hi
    by_cases hx : L x <;> simp [hx] at ht <;>
      simp [ht, Constraint.triv, Constraint.reject] at hi
  · intro x hx
    exact ⟨fun _ => false, by simp [hx, acceptProb, Constraint.sat, Constraint.triv]⟩
  · intro x hx a
    simp [hx, acceptProb, Constraint.sat, Constraint.reject]
    norm_num

theorem exists_model_gapPCP : ∃ M : EffModel, GapPCP M :=
  ⟨trivialModel, fun L _ => gapVerifier_trivialModel L⟩

/-- The hypotheses of `pcp_theorem_of_gap_npHard` are satisfiable as well: in the degenerate
model the singleton language `{[true]}` is NP-hard and has a constant-gap PCP. -/
theorem exists_model_npHard_gapVerifier :
    ∃ (M : EffModel) (K : Lang), NPHard M K ∧ GapVerifier M K := by
  classical
  refine ⟨trivialModel, fun w => w = [true], ?_, gapVerifier_trivialModel _⟩
  intro L _
  refine ⟨fun x => if L x then [true] else [false], ⟨1, ?_⟩, ?_⟩
  · intro x
    by_cases hx : L x <;> simp [hx]
  · intro x
    by_cases hx : L x <;> simp [hx]

end CS

#print axioms CS.pcp_theorem
#print axioms CS.pcp_theorem_iff_gapPCP
#print axioms CS.exists_model_gapPCP
#print axioms CS.pcp_theorem_of_gap_npHard
#print axioms CS.exists_model_npHard_gapVerifier

