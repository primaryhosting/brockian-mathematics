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

set_option grind.warning false

namespace CS

/-! ## Polynomial bounds -/

/-- `PolyBd f` says that `f : ℕ → ℕ` is bounded by a polynomial. -/
def PolyBd (f : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ n : ℕ, f n ≤ (n + 2) ^ c

theorem polyBd_mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : PolyBd g) : PolyBd f := by
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, fun n => (h n).trans (hc n)⟩

theorem polyBd_const (k : ℕ) : PolyBd (fun _ => k) := by
  refine ⟨k, fun n => ?_⟩
  calc k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_two_pow_self)
    _ ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k

theorem polyBd_add {f g : ℕ → ℕ} (hf : PolyBd f) (hg : PolyBd g) :
    PolyBd (fun n => f n + g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b + 1, fun n => ?_⟩
  have h1 : f n ≤ (n + 2) ^ (a + b) :=
    (ha n).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : g n ≤ (n + 2) ^ (a + b) :=
    (hb n).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have he : (n + 2) ^ (a + b + 1) = (n + 2) ^ (a + b) * (n + 2) := by ring
  have h3 : (n + 2) ^ (a + b) * 2 ≤ (n + 2) ^ (a + b) * (n + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  show f n + g n ≤ (n + 2) ^ (a + b + 1)
  omega

theorem polyBd_mul {f g : ℕ → ℕ} (hf : PolyBd f) (hg : PolyBd g) :
    PolyBd (fun n => f n * g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, fun n => ?_⟩
  calc f n * g n ≤ (n + 2) ^ a * (n + 2) ^ b := Nat.mul_le_mul (ha n) (hb n)
    _ = (n + 2) ^ (a + b) := (pow_add _ _ _).symm

/-! ## Boolean circuits -/

/-- Boolean circuits with `n` input variables, built from constants, variables,
negation, conjunction and disjunction. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n

namespace Circuit

/-- Value of a circuit on a given assignment of its input variables. -/
def eval {n : ℕ} : Circuit n → (Fin n → Bool) → Bool
  | .const b, _ => b
  | .var i, v => v i
  | .not c, v => !(c.eval v)
  | .and c d, v => (c.eval v) && (d.eval v)
  | .or c d, v => (c.eval v) || (d.eval v)

/-- Number of gates (including inputs) of a circuit. -/
def size {n : ℕ} : Circuit n → ℕ
  | .const _ => 1
  | .var _ => 1
  | .not c => c.size + 1
  | .and c d => c.size + d.size + 1
  | .or c d => c.size + d.size + 1

theorem one_le_size {n : ℕ} (c : Circuit n) : 1 ≤ c.size := by
  cases c <;> simp [size]

/-- Substitute a circuit into each input variable. -/
def subst {k N : ℕ} : Circuit k → (Fin k → Circuit N) → Circuit N
  | .const b, _ => .const b
  | .var i, f => f i
  | .not c, f => .not (c.subst f)
  | .and c d, f => .and (c.subst f) (d.subst f)
  | .or c d, f => .or (c.subst f) (d.subst f)

@[simp] theorem eval_subst {k N : ℕ} (c : Circuit k) (f : Fin k → Circuit N)
    (v : Fin N → Bool) : (c.subst f).eval v = c.eval (fun i => (f i).eval v) := by
  induction c <;> simp [subst, eval, *]

theorem size_subst_le {k N : ℕ} (c : Circuit k) (f : Fin k → Circuit N) (M : ℕ)
    (hf : ∀ i, (f i).size ≤ M) : (c.subst f).size ≤ c.size * (M + 1) := by
  induction c with
  | const b => simp [subst, size]
  | var i => simpa [subst, size] using (hf i).trans (Nat.le_succ M)
  | not c ih => simp only [subst, size]; nlinarith [ih]
  | and c d ihc ihd => simp only [subst, size]; nlinarith [ihc, ihd]
  | or c d ihc ihd => simp only [subst, size]; nlinarith [ihc, ihd]

/-- Conjunction of a list of circuits. -/
def bigAnd {N : ℕ} : List (Circuit N) → Circuit N
  | [] => .const true
  | c :: cs => .and c (bigAnd cs)

@[simp] theorem eval_bigAnd {N : ℕ} (l : List (Circuit N)) (v : Fin N → Bool) :
    (bigAnd l).eval v = true ↔ ∀ c ∈ l, c.eval v = true := by
  induction l with
  | nil => simp [bigAnd, eval]
  | cons c cs ih => simp [bigAnd, eval, ih]

theorem size_bigAnd_le {N : ℕ} (l : List (Circuit N)) (M : ℕ)
    (hl : ∀ c ∈ l, c.size ≤ M) : (bigAnd l).size ≤ l.length * (M + 1) + 1 := by
  induction l with
  | nil => simp [bigAnd, size]
  | cons c cs ih =>
      have h1 : c.size ≤ M := hl c (by simp)
      have h2 := ih (fun d hd => hl d (by simp [hd]))
      simp only [bigAnd, size, List.length_cons]
      nlinarith [h1, h2]

/-- The biconditional of two circuits. -/
def iff {N : ℕ} (c d : Circuit N) : Circuit N :=
  .or (.and c d) (.and (.not c) (.not d))

@[simp] theorem eval_iff {N : ℕ} (c d : Circuit N) (v : Fin N → Bool) :
    (Circuit.iff c d).eval v = true ↔ (c.eval v = d.eval v) := by
  simp only [Circuit.iff, eval]
  cases hc : c.eval v <;> cases hd : d.eval v <;> simp

theorem size_iff {N : ℕ} (c d : Circuit N) :
    (Circuit.iff c d).size = 2 * c.size + 2 * d.size + 5 := by
  simp [Circuit.iff, size]; ring

/-- The implication of two circuits. -/
def imp {N : ℕ} (c d : Circuit N) : Circuit N := .or (.not c) d

@[simp] theorem eval_imp {N : ℕ} (c d : Circuit N) (v : Fin N → Bool) :
    (Circuit.imp c d).eval v = true ↔ (c.eval v = true → d.eval v = true) := by
  simp only [Circuit.imp, eval]
  cases hc : c.eval v <;> cases hd : d.eval v <;> simp

theorem size_imp {N : ℕ} (c d : Circuit N) :
    (Circuit.imp c d).size = c.size + d.size + 2 := by
  simp [Circuit.imp, size]; ring

end Circuit

/-! ## Languages, nonuniform NP and PCP verifiers -/

/-- A language: for every input length `n`, a set of `n`-bit strings. -/
def Language := (n : ℕ) → (Fin n → Bool) → Prop

/-- `NPpoly L` is the (nonuniform, circuit based) class `NP/poly`:  membership in `L`
is witnessed by a short certificate that is checked by a polynomial size circuit. -/
def NPpoly (L : Language) : Prop :=
  ∃ (w : ℕ → ℕ) (C : (n : ℕ) → Circuit (n + w n)),
    PolyBd w ∧ PolyBd (fun n => (C n).size) ∧
      ∀ (n : ℕ) (x : Fin n → Bool),
        L n x ↔ ∃ y : Fin (w n) → Bool, (C n).eval (Fin.append x y) = true

/-- A probabilistically checkable proof verifier for inputs of length `n`.
It tosses `rlen` coins, makes `qnum` (nonadaptive) queries to a proof whose positions are
indexed by `plen`-bit strings, and decides.  The `i`-th queried position is computed,
bit by bit, by the circuits `query i j` from the input and the random string, and the
final decision is computed by the circuit `dec` from the input, the random string and
the `qnum` answer bits. -/
structure PCPVerifier (n : ℕ) where
  /-- number of random bits -/
  rlen : ℕ
  /-- number of queries into the proof -/
  qnum : ℕ
  /-- proof positions are indexed by bit strings of this length -/
  plen : ℕ
  /-- `query i j` computes the `j`-th bit of the `i`-th queried position -/
  query : Fin qnum → Fin plen → Circuit (n + rlen)
  /-- the decision circuit -/
  dec : Circuit (n + rlen + qnum)

namespace PCPVerifier

variable {n : ℕ}

/-- Total size of the circuits describing the verifier. -/
def size (V : PCPVerifier n) : ℕ := (∑ i, ∑ j, (V.query i j).size) + V.dec.size

/-- The answers the proof `pi` gives to the queries of `V` on input `x` and randomness `r`. -/
def answers (V : PCPVerifier n) (x : Fin n → Bool) (r : Fin V.rlen → Bool)
    (pi : (Fin V.plen → Bool) → Bool) : Fin V.qnum → Bool :=
  fun i => pi (fun j => (V.query i j).eval (Fin.append x r))

/-- Whether `V` accepts input `x` with randomness `r` and proof `pi`. -/
def accepts (V : PCPVerifier n) (x : Fin n → Bool) (r : Fin V.rlen → Bool)
    (pi : (Fin V.plen → Bool) → Bool) : Bool :=
  V.dec.eval (Fin.append (Fin.append x r) (V.answers x r pi))

end PCPVerifier

/-- `PCPlog1 L` says that `L ∈ PCP(log n, 1)`:  there is a polynomial size verifier using
logarithmically many random bits (equivalently: polynomially many random strings) and a
constant number `q` of queries, with perfect completeness and soundness error `1/2`. -/
def PCPlog1 (L : Language) : Prop :=
  ∃ (V : (n : ℕ) → PCPVerifier n) (q : ℕ),
    (∀ n, (V n).qnum = q) ∧
    PolyBd (fun n => 2 ^ (V n).rlen) ∧
    PolyBd (fun n => (V n).size) ∧
    (∀ (n : ℕ) (x : Fin n → Bool), L n x →
      ∃ pi : (Fin (V n).plen → Bool) → Bool, ∀ r, (V n).accepts x r pi = true) ∧
    (∀ (n : ℕ) (x : Fin n → Bool), ¬ L n x →
      ∀ pi : (Fin (V n).plen → Bool) → Bool,
        2 * ({r : Fin (V n).rlen → Bool | (V n).accepts x r pi = true} :
              Finset (Fin (V n).rlen → Bool)).card ≤ 2 ^ (V n).rlen)

/-! ## From a PCP verifier to an NP certificate

Given a PCP verifier we build a polynomial size circuit whose satisfying assignments are
exactly the *locally consistent answer tables*: an assignment of a bit to every pair
(random string, query index) which makes the verifier accept for every random string and
which is consistent, i.e. gives the same bit to two queries landing on the same position
of the proof.  Such a table exists iff there is a proof accepted with probability one.
-/

namespace PCPVerifier

variable {n : ℕ}

noncomputable section

/-- Length of the NP certificate: one bit for every (random string, query) pair. -/
def wlen (V : PCPVerifier n) : ℕ := 2 ^ V.rlen * V.qnum

/-- Indexing of the certificate bits by (random string, query) pairs. -/
def enc (V : PCPVerifier n) : ((Fin V.rlen → Bool) × Fin V.qnum) ≃ Fin V.wlen :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_bool]
    rfl)

/-- The circuit reading the `j`-th input bit. -/
def xv (V : PCPVerifier n) (j : Fin n) : Circuit (n + V.wlen) := .var (Fin.castAdd _ j)

/-- The circuit reading the certificate bit for the pair `(r, i)`. -/
def av (V : PCPVerifier n) (r : Fin V.rlen → Bool) (i : Fin V.qnum) : Circuit (n + V.wlen) :=
  .var (Fin.natAdd n (V.enc (r, i)))

/-- Substitution feeding the input bits and the hard-wired random string `r`. -/
def sxr (V : PCPVerifier n) (r : Fin V.rlen → Bool) : Fin (n + V.rlen) → Circuit (n + V.wlen) :=
  Fin.append V.xv (fun k => .const (r k))

/-- Circuit computing the `j`-th bit of the `i`-th query position, for randomness `r`. -/
def posC (V : PCPVerifier n) (r : Fin V.rlen → Bool) (i : Fin V.qnum) (j : Fin V.plen) :
    Circuit (n + V.wlen) := (V.query i j).subst (V.sxr r)

/-- Circuit running the verifier's decision on randomness `r`, reading the answers off
the certificate. -/
def decC (V : PCPVerifier n) (r : Fin V.rlen → Bool) : Circuit (n + V.wlen) :=
  V.dec.subst (Fin.append (V.sxr r) (fun i => V.av r i))

/-- Circuit testing that two queries address the same proof position. -/
def eqC (V : PCPVerifier n) (r : Fin V.rlen → Bool) (i : Fin V.qnum)
    (r' : Fin V.rlen → Bool) (i' : Fin V.qnum) : Circuit (n + V.wlen) :=
  Circuit.bigAnd ((List.finRange V.plen).map fun j => Circuit.iff (V.posC r i j) (V.posC r' i' j))

/-- Circuit checking consistency of the answers to two queries. -/
def consC (V : PCPVerifier n) (r : Fin V.rlen → Bool) (i : Fin V.qnum)
    (r' : Fin V.rlen → Bool) (i' : Fin V.qnum) : Circuit (n + V.wlen) :=
  Circuit.imp (V.eqC r i r' i') (Circuit.iff (V.av r i) (V.av r' i'))

/-- All the checks the NP circuit performs. -/
def npList (V : PCPVerifier n) : List (Circuit (n + V.wlen)) :=
  ((Finset.univ : Finset (Fin V.rlen → Bool)).toList.map V.decC) ++
    ((Finset.univ : Finset ((((Fin V.rlen → Bool) × Fin V.qnum)) ×
      (((Fin V.rlen → Bool) × Fin V.qnum)))).toList.map
        fun p => V.consC p.1.1 p.1.2 p.2.1 p.2.2)

/-- The NP verification circuit associated with a PCP verifier. -/
def npCircuit (V : PCPVerifier n) : Circuit (n + V.wlen) := Circuit.bigAnd V.npList

variable (V : PCPVerifier n) (x : Fin n → Bool) (y : Fin V.wlen → Bool)

@[simp] theorem eval_xv (j : Fin n) : (V.xv j).eval (Fin.append x y) = x j := by
  simp [xv, Circuit.eval]

@[simp] theorem eval_av (r : Fin V.rlen → Bool) (i : Fin V.qnum) :
    (V.av r i).eval (Fin.append x y) = y (V.enc (r, i)) := by
  simp [av, Circuit.eval]

theorem eval_sxr (r : Fin V.rlen → Bool) (k : Fin (n + V.rlen)) :
    ((V.sxr r) k).eval (Fin.append x y) = Fin.append x r k := by
  induction k using Fin.addCases with
  | left j => simp [sxr]
  | right j => simp [sxr, Circuit.eval]

@[simp] theorem eval_posC (r : Fin V.rlen → Bool) (i : Fin V.qnum) (j : Fin V.plen) :
    (V.posC r i j).eval (Fin.append x y) = (V.query i j).eval (Fin.append x r) := by
  simp only [posC, Circuit.eval_subst]
  exact congrArg _ (funext fun k => eval_sxr V x y r k)

@[simp] theorem eval_decC (r : Fin V.rlen → Bool) :
    (V.decC r).eval (Fin.append x y) =
      V.dec.eval (Fin.append (Fin.append x r) (fun i => y (V.enc (r, i)))) := by
  simp only [decC, Circuit.eval_subst]
  refine congrArg _ (funext fun k => ?_)
  induction k using Fin.addCases with
  | left j => simp [eval_sxr]
  | right j => simp

@[simp] theorem eval_eqC (r : Fin V.rlen → Bool) (i : Fin V.qnum)
    (r' : Fin V.rlen → Bool) (i' : Fin V.qnum) :
    (V.eqC r i r' i').eval (Fin.append x y) = true ↔
      ∀ j, (V.query i j).eval (Fin.append x r) = (V.query i' j).eval (Fin.append x r') := by
  simp [eqC]

@[simp] theorem eval_consC (r : Fin V.rlen → Bool) (i : Fin V.qnum)
    (r' : Fin V.rlen → Bool) (i' : Fin V.qnum) :
    (V.consC r i r' i').eval (Fin.append x y) = true ↔
      ((∀ j, (V.query i j).eval (Fin.append x r) = (V.query i' j).eval (Fin.append x r')) →
        y (V.enc (r, i)) = y (V.enc (r', i'))) := by
  simp [consC]

theorem eval_npCircuit :
    V.npCircuit.eval (Fin.append x y) = true ↔
      ((∀ r, V.dec.eval (Fin.append (Fin.append x r) (fun i => y (V.enc (r, i)))) = true) ∧
        (∀ r i r' i',
          (∀ j, (V.query i j).eval (Fin.append x r) = (V.query i' j).eval (Fin.append x r')) →
            y (V.enc (r, i)) = y (V.enc (r', i')))) := by
  simp only [npCircuit, Circuit.eval_bigAnd, npList, List.mem_append, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨fun r => ?_, fun r i r' i' hq => ?_⟩
    · simpa using h (V.decC r) (Or.inl ⟨r, rfl⟩)
    · exact (eval_consC V x y r i r' i').1
        (h (V.consC r i r' i') (Or.inr ⟨((r, i), (r', i')), rfl⟩)) hq
  · rintro ⟨h1, h2⟩ c (⟨r, rfl⟩ | ⟨p, rfl⟩)
    · simpa using h1 r
    · exact (eval_consC V x y p.1.1 p.1.2 p.2.1 p.2.2).2 (h2 p.1.1 p.1.2 p.2.1 p.2.2)

/-- If some proof is accepted with probability one, the associated NP circuit is
satisfiable. -/
theorem exists_sat_of_exists_proof
    (h : ∃ pi : (Fin V.plen → Bool) → Bool, ∀ r, V.accepts x r pi = true) :
    ∃ y : Fin V.wlen → Bool, V.npCircuit.eval (Fin.append x y) = true := by
  obtain ⟨pi, hpi⟩ := h
  refine ⟨fun k => pi (fun j => (V.query (V.enc.symm k).2 j).eval
    (Fin.append x (V.enc.symm k).1)), ?_⟩
  have key : ∀ (r : Fin V.rlen → Bool) (i : Fin V.qnum),
      (fun k => pi (fun j => (V.query (V.enc.symm k).2 j).eval
        (Fin.append x (V.enc.symm k).1))) (V.enc (r, i))
        = pi (fun j => (V.query i j).eval (Fin.append x r)) := by
    intro r i
    simp
  rw [eval_npCircuit]
  refine ⟨fun r => ?_, fun r i r' i' hq => ?_⟩
  · have h := hpi r
    simp only [accepts] at h
    refine Eq.trans ?_ h
    exact congrArg (fun f => V.dec.eval (Fin.append (Fin.append x r) f)) (funext fun i => key r i)
  · simp only [Equiv.symm_apply_apply]
    exact congrArg pi (funext hq)

/-- Conversely, a satisfying assignment of the NP circuit yields a proof that is accepted
with probability one. -/
theorem exists_proof_of_exists_sat
    (h : ∃ y : Fin V.wlen → Bool, V.npCircuit.eval (Fin.append x y) = true) :
    ∃ pi : (Fin V.plen → Bool) → Bool, ∀ r, V.accepts x r pi = true := by
  obtain ⟨y, hy⟩ := h
  rw [eval_npCircuit] at hy
  obtain ⟨h1, h2⟩ := hy
  classical
  refine ⟨fun p => if hp : ∃ ri : (Fin V.rlen → Bool) × Fin V.qnum,
      (fun j => (V.query ri.2 j).eval (Fin.append x ri.1)) = p then y (V.enc hp.choose)
      else false, ?_⟩
  have key : ∀ (r : Fin V.rlen → Bool) (i : Fin V.qnum),
      (if hp : ∃ ri : (Fin V.rlen → Bool) × Fin V.qnum,
          (fun j => (V.query ri.2 j).eval (Fin.append x ri.1))
            = (fun j => (V.query i j).eval (Fin.append x r))
        then y (V.enc hp.choose) else false) = y (V.enc (r, i)) := by
    intro r i
    have hex : ∃ ri : (Fin V.rlen → Bool) × Fin V.qnum,
        (fun j => (V.query ri.2 j).eval (Fin.append x ri.1))
          = (fun j => (V.query i j).eval (Fin.append x r)) := ⟨(r, i), rfl⟩
    rw [dif_pos hex]
    exact h2 hex.choose.1 hex.choose.2 r i (fun j => congrFun hex.choose_spec j)
  intro r
  simp only [accepts]
  refine Eq.trans ?_ (h1 r)
  exact congrArg (fun f => V.dec.eval (Fin.append (Fin.append x r) f)) (funext fun i => key r i)

/-! ### Size of the constructed circuit -/

theorem dec_size_le : V.dec.size ≤ V.size := Nat.le_add_left _ _

theorem query_size_le (i : Fin V.qnum) (j : Fin V.plen) : (V.query i j).size ≤ V.size := by
  have h1 : (V.query i j).size ≤ ∑ j', (V.query i j').size :=
    Finset.single_le_sum (f := fun j' => (V.query i j').size)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 : (∑ j', (V.query i j').size) ≤ ∑ i', ∑ j', (V.query i' j').size :=
    Finset.single_le_sum (f := fun i' => ∑ j', (V.query i' j').size)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (h1.trans h2).trans (Nat.le_add_right _ _)

theorem plen_le (hq : 0 < V.qnum) : V.plen ≤ V.size := by
  have h1 : ∑ _i : Fin V.qnum, ∑ _j : Fin V.plen, 1 ≤ ∑ i, ∑ j, (V.query i j).size :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Circuit.one_le_size _
  have h2 : ∑ _i : Fin V.qnum, ∑ _j : Fin V.plen, 1 = V.qnum * V.plen := by
    simp [Finset.sum_const]
  have h3 : V.plen ≤ V.qnum * V.plen := Nat.le_mul_of_pos_left _ hq
  have h4 : (∑ i, ∑ j, (V.query i j).size) ≤ V.size := Nat.le_add_right _ _
  omega

theorem size_sxr_le (r : Fin V.rlen → Bool) (k : Fin (n + V.rlen)) : (V.sxr r k).size ≤ 1 := by
  induction k using Fin.addCases with
  | left j => simp [sxr, xv, Circuit.size]
  | right j => simp [sxr, Circuit.size]

theorem size_decC_le (r : Fin V.rlen → Bool) : (V.decC r).size ≤ 2 * V.size := by
  have hsub : ∀ k, ((Fin.append (V.sxr r) (fun i => V.av r i)) k).size ≤ 1 := by
    intro k
    induction k using Fin.addCases with
    | left j => simpa using size_sxr_le V r j
    | right j => simp [av, Circuit.size]
  have := Circuit.size_subst_le V.dec (Fin.append (V.sxr r) (fun i => V.av r i)) 1 hsub
  have hd := dec_size_le V
  simp only [decC]
  omega

theorem size_posC_le (r : Fin V.rlen → Bool) (i : Fin V.qnum) (j : Fin V.plen) :
    (V.posC r i j).size ≤ 2 * V.size := by
  have := Circuit.size_subst_le (V.query i j) (V.sxr r) 1 (size_sxr_le V r)
  have hq := query_size_le V i j
  simp only [posC]
  omega

theorem size_eqC_le (r : Fin V.rlen → Bool) (i : Fin V.qnum)
    (r' : Fin V.rlen → Bool) (i' : Fin V.qnum) :
    (V.eqC r i r' i').size ≤ V.plen * (8 * V.size + 6) + 1 := by
  have hb : ∀ c ∈ (List.finRange V.plen).map
      (fun j => Circuit.iff (V.posC r i j) (V.posC r' i' j)), c.size ≤ 8 * V.size + 5 := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨j, _, rfl⟩ := hc
    rw [Circuit.size_iff]
    have h1 := size_posC_le V r i j
    have h2 := size_posC_le V r' i' j
    omega
  have := Circuit.size_bigAnd_le _ _ hb
  simpa [eqC] using this

theorem size_consC_le (hq : 0 < V.qnum) (r : Fin V.rlen → Bool) (i : Fin V.qnum)
    (r' : Fin V.rlen → Bool) (i' : Fin V.qnum) :
    (V.consC r i r' i').size ≤ 8 * V.size * V.size + 6 * V.size + 12 := by
  have h1 := size_eqC_le V r i r' i'
  have h2 : V.plen ≤ V.size := plen_le V hq
  have h3 : V.plen * (8 * V.size + 6) ≤ V.size * (8 * V.size + 6) :=
    Nat.mul_le_mul_right _ h2
  have h4 : (Circuit.iff (V.av r i) (V.av r' i')).size = 9 := by
    rw [Circuit.size_iff]; simp [av, Circuit.size]
  rw [consC, Circuit.size_imp, h4]
  nlinarith [h1, h3]

theorem length_npList : V.npList.length = 2 ^ V.rlen + (2 ^ V.rlen * V.qnum) * (2 ^ V.rlen * V.qnum) := by
  simp only [npList, List.length_append, List.length_map, Finset.length_toList, Finset.card_univ]
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool]
  simp

theorem size_npCircuit_le :
    V.npCircuit.size ≤
      (2 ^ V.rlen + (2 ^ V.rlen * V.qnum) * (2 ^ V.rlen * V.qnum)) *
        (8 * V.size * V.size + 6 * V.size + 13) + 1 := by
  have hb : ∀ c ∈ V.npList, c.size ≤ 8 * V.size * V.size + 6 * V.size + 12 := by
    intro c hc
    simp only [npList, List.mem_append, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and] at hc
    rcases hc with ⟨r, rfl⟩ | ⟨p, rfl⟩
    · have := size_decC_le V r
      nlinarith [this, Nat.zero_le V.size]
    · exact size_consC_le V (Fin.pos p.1.2) p.1.1 p.1.2 p.2.1 p.2.2
  have := Circuit.size_bigAnd_le V.npList _ hb
  rw [length_npList] at this
  simpa [npCircuit] using this

end

end PCPVerifier

/-! ## The easy inclusion `PCP(log n, 1) ⊆ NP` -/

/-- **Every language with a logarithmic randomness, constant query PCP verifier is in NP.**
The certificate is a locally consistent table of answers to all the (polynomially many)
queries the verifier can make, and the NP circuit checks acceptance for every random
string together with the consistency of the table. -/
theorem pcp_subset_np (L : Language) (h : PCPlog1 L) : NPpoly L := by
  obtain ⟨V, q, hq, hR, hS, hcomp, hsound⟩ := h
  have hQ : PolyBd (fun n => (V n).qnum) :=
    polyBd_mono (fun n => le_of_eq (hq n)) (polyBd_const q)
  refine ⟨fun n => (V n).wlen, fun n => (V n).npCircuit, ?_, ?_, ?_⟩
  · exact polyBd_mono (fun n => le_of_eq rfl) (polyBd_mul hR hQ)
  · refine polyBd_mono (fun n => PCPVerifier.size_npCircuit_le (V n)) ?_
    exact polyBd_add
      (polyBd_mul (polyBd_add hR (polyBd_mul (polyBd_mul hR hQ) (polyBd_mul hR hQ)))
        (polyBd_add (polyBd_add (polyBd_mul (polyBd_mul (polyBd_const 8) hS) hS)
          (polyBd_mul (polyBd_const 6) hS)) (polyBd_const 13)))
      (polyBd_const 1)
  · intro n x
    constructor
    · intro hx
      exact PCPVerifier.exists_sat_of_exists_proof (V n) x (hcomp n x hx)
    · intro hy
      by_contra hnx
      obtain ⟨pi, hpi⟩ := PCPVerifier.exists_proof_of_exists_sat (V n) x hy
      have hs := hsound n x hnx pi
      have hcard : ({r : Fin (V n).rlen → Bool | (V n).accepts x r pi = true} :
          Finset (Fin (V n).rlen → Bool)).card = 2 ^ (V n).rlen := by
        rw [Finset.filter_true_of_mem (fun r _ => hpi r), Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin]
      rw [hcard] at hs
      have : 0 < 2 ^ (V n).rlen := Nat.two_pow_pos _
      omega

/-! ## The PCP theorem -/

/-- **The PCP theorem**: `NP = PCP(log n, 1)`.

The inclusion `PCP(log n, 1) ⊆ NP` is proved here (`CS.pcp_subset_np`); the reverse
inclusion `NP ⊆ PCP(log n, 1)`, which is the deep content of the PCP theorem
(Arora–Safra, Arora–Lund–Motwani–Sudan; Dinur), is taken as the hypothesis `hard`. -/
theorem pcp_theorem (hard : ∀ L : Language, NPpoly L → PCPlog1 L) :
    {L : Language | NPpoly L} = {L : Language | PCPlog1 L} := by
  ext L
  exact ⟨hard L, pcp_subset_np L⟩

end CS

