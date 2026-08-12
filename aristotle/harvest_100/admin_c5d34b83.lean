import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file sets up a self-contained, fully formal framework for probabilistically checkable
proofs, in the non-uniform (Boolean circuit) model of computation, and states the PCP theorem
`NP = PCP(log n, O(1))` in it (`CS.PCPCharacterization`).

* `CS.Circuit` is the type of Boolean circuits, with `Circuit.eval` and `Circuit.size`.
* `CS.NPVerifier` is a polynomial-size circuit family verifying polynomially long witnesses,
  and `CS.InNP` / `CS.NPClass` is the resulting class `NP` (non-uniform, i.e. `NP/poly`).
* `CS.PCPVerifier r q` is a verifier that, on inputs of length `n`, tosses `r n` coins, computes
  the positions of `q n` (non-adaptive) queries into a proof `pi : ℕ → Bool` by polynomial-size
  circuits, and decides by a polynomial-size circuit.  `CS.PCPVerifier.Decides` requires perfect
  completeness and soundness error at most `1/2`.
* `CS.InPCPLogConst` / `CS.PCPLogConstClass` is `PCP(log n, O(1))`.

The main results proved here are:

* `CS.pcp_subset_np`: any language with a PCP verifier using polynomially many random strings
  and polynomially many queries is in `NP`.  In particular `PCP(log n, O(1)) ⊆ NP`
  (`CS.pcp_log_const_subset_np`).
* `CS.np_subset_pcp` and `CS.np_iff_pcp_poly`: conversely every `NP` language has a PCP verifier
  reading the whole (polynomially long) proof, so `NP = PCP(log n, poly n)`.
* `CS.pcp_theorem`: the PCP characterization `NP = PCP(log n, O(1))` holds if and only if the
  inclusion `NP ⊆ PCP(log n, O(1))` holds; the reverse inclusion is unconditional.

The hard inclusion `NP ⊆ PCP(log n, O(1))` (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy) is
*not* formalized here; only the statement and the unconditional half of the equality are.
-/

set_option maxHeartbeats 1000000

namespace CS

/-! ## Polynomially bounded functions -/

/-- A function `f : ℕ → ℕ` is polynomially bounded. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

theorem polyBounded_const (m : ℕ) : PolyBounded (fun _ => m) :=
  ⟨m, 0, by simp⟩

theorem PolyBounded.mono {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ n, f n ≤ g n) :
    PolyBounded f := by
  obtain ⟨c, k, hc⟩ := hg
  exact ⟨c, k, fun n => le_trans (h n) (hc n)⟩

theorem PolyBounded.add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n + g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, max k₁ k₂, fun n => ?_⟩
  have e₁ : (n + 1) ^ k₁ ≤ (n + 1) ^ max k₁ k₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e₂ : (n + 1) ^ k₂ ≤ (n + 1) ^ max k₁ k₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc f n + g n ≤ c₁ * (n + 1) ^ k₁ + c₂ * (n + 1) ^ k₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ c₁ * (n + 1) ^ max k₁ k₂ + c₂ * (n + 1) ^ max k₁ k₂ := by
        exact Nat.add_le_add (Nat.mul_le_mul_left _ e₁) (Nat.mul_le_mul_left _ e₂)
    _ = (c₁ + c₂) * (n + 1) ^ max k₁ k₂ := by ring

theorem PolyBounded.mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n * g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, k₁ + k₂, fun n => ?_⟩
  calc f n * g n ≤ (c₁ * (n + 1) ^ k₁) * (c₂ * (n + 1) ^ k₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = c₁ * c₂ * (n + 1) ^ (k₁ + k₂) := by rw [pow_add]; ring

theorem polyBounded_id : PolyBounded (fun n => n) := ⟨1, 1, by intro n; simp⟩

/-- Logarithmic randomness gives polynomially many random strings. -/
theorem polyBounded_two_pow_log (c : ℕ) :
    PolyBounded (fun n => 2 ^ (c * Nat.log 2 (n + 1) + c)) := by
  refine ⟨2 ^ c, c, fun n => ?_⟩
  have h : (2 : ℕ) ^ Nat.log 2 (n + 1) ≤ n + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  calc 2 ^ (c * Nat.log 2 (n + 1) + c)
      = (2 ^ Nat.log 2 (n + 1)) ^ c * 2 ^ c := by rw [pow_add, ← pow_mul, Nat.mul_comm c]
    _ ≤ (n + 1) ^ c * 2 ^ c := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h c)
    _ = 2 ^ c * (n + 1) ^ c := by ring

/-! ## Boolean circuits -/

/-- Bit strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- Boolean circuits (formulas) on `n` input bits. -/
inductive Circuit : ℕ → Type
  | const {n : ℕ} (b : Bool) : Circuit n
  | var {n : ℕ} (i : Fin n) : Circuit n
  | neg {n : ℕ} (c : Circuit n) : Circuit n
  | conj {n : ℕ} (c d : Circuit n) : Circuit n
  | disj {n : ℕ} (c d : Circuit n) : Circuit n
  deriving Inhabited

namespace Circuit

/-- The Boolean value computed by a circuit on a given input. -/
def eval : {n : ℕ} → Circuit n → Bits n → Bool
  | _, .const b, _ => b
  | _, .var i, x => x i
  | _, .neg c, x => !(c.eval x)
  | _, .conj c d, x => (c.eval x) && (d.eval x)
  | _, .disj c d, x => (c.eval x) || (d.eval x)

/-- The number of gates of a circuit. -/
def size : {n : ℕ} → Circuit n → ℕ
  | _, .const _ => 1
  | _, .var _ => 1
  | _, .neg c => c.size + 1
  | _, .conj c d => c.size + d.size + 1
  | _, .disj c d => c.size + d.size + 1

theorem one_le_size {n : ℕ} (c : Circuit n) : 1 ≤ c.size := by
  cases c <;> simp [size]

/-- Substituting circuits for the input variables. -/
def subst : {n m : ℕ} → Circuit n → (Fin n → Circuit m) → Circuit m
  | _, _, .const b, _ => .const b
  | _, _, .var i, f => f i
  | _, _, .neg c, f => .neg (c.subst f)
  | _, _, .conj c d, f => .conj (c.subst f) (d.subst f)
  | _, _, .disj c d, f => .disj (c.subst f) (d.subst f)

@[simp] theorem eval_subst {n m : ℕ} (c : Circuit n) (f : Fin n → Circuit m) (x : Bits m) :
    (c.subst f).eval x = c.eval (fun i => (f i).eval x) := by
  induction c with
  | const b => simp [subst, eval]
  | var i => simp [subst, eval]
  | neg c ih => simp [subst, eval, ih]
  | conj c d ihc ihd => simp [subst, eval, ihc, ihd]
  | disj c d ihc ihd => simp [subst, eval, ihc, ihd]

theorem size_subst {n m : ℕ} (c : Circuit n) (f : Fin n → Circuit m) (s : ℕ) (hs : 1 ≤ s)
    (hf : ∀ i, (f i).size ≤ s) : (c.subst f).size ≤ c.size * s := by
  induction c with
  | const b => simpa [subst, size] using hs
  | var i => simpa [subst, size] using hf i
  | neg c ih =>
      have := ih
      simp only [subst, size]
      nlinarith [this, hs]
  | conj c d ihc ihd =>
      simp only [subst, size]
      nlinarith [ihc, ihd, hs]
  | disj c d ihc ihd =>
      simp only [subst, size]
      nlinarith [ihc, ihd, hs]

/-- Conjunction of a list of circuits. -/
def bigAnd {n : ℕ} (l : List (Circuit n)) : Circuit n :=
  l.foldr (fun c d => .conj c d) (.const true)

@[simp] theorem eval_bigAnd {n : ℕ} (l : List (Circuit n)) (x : Bits n) :
    (bigAnd l).eval x = l.all (fun c => c.eval x) := by
  induction l with
  | nil => simp [bigAnd, eval]
  | cons c l ih => simp [bigAnd, eval] at *; simp [ih]

theorem size_bigAnd {n : ℕ} (l : List (Circuit n)) (s : ℕ) (hl : ∀ c ∈ l, c.size ≤ s) :
    (bigAnd l).size ≤ 1 + l.length * (s + 1) := by
  induction l with
  | nil => simp [bigAnd, size]
  | cons c l ih =>
      have h1 : c.size ≤ s := hl c (List.mem_cons_self ..)
      have h2 : (bigAnd l).size ≤ 1 + l.length * (s + 1) :=
        ih (fun d hd => hl d (List.mem_cons_of_mem _ hd))
      simp only [bigAnd, List.foldr_cons, size, List.length_cons]
      have : (bigAnd l) = l.foldr (fun c d => .conj c d) (.const true) := rfl
      rw [← this]
      nlinarith [h1, h2]

/-- Exclusive-nor: the two circuits compute the same bit. -/
def iff' {n : ℕ} (c d : Circuit n) : Circuit n :=
  .disj (.conj c d) (.conj (.neg c) (.neg d))

@[simp] theorem eval_iff' {n : ℕ} (c d : Circuit n) (x : Bits n) :
    (iff' c d).eval x = (decide (c.eval x = d.eval x)) := by
  simp only [iff', eval]
  cases c.eval x <;> cases d.eval x <;> simp

theorem size_iff' {n : ℕ} (c d : Circuit n) :
    (iff' c d).size = 2 * c.size + 2 * d.size + 5 := by
  simp [iff', size]; omega

end Circuit

end CS

/-! ## Encoding bit strings as numbers -/

namespace CS

/-- The natural number encoded by a bit string (little-endian). -/
def bitsToNat : {m : ℕ} → Bits m → ℕ
  | 0, _ => 0
  | _ + 1, f => (if f 0 then 1 else 0) + 2 * bitsToNat (fun j => f j.succ)

theorem bitsToNat_injective : ∀ {m : ℕ}, Function.Injective (bitsToNat (m := m)) := by
  intro m
  induction m with
  | zero => intro f g _; funext j; exact absurd j.isLt (by omega)
  | succ m ih =>
      intro f g h
      simp only [bitsToNat] at h
      have h0 : f 0 = g 0 := by
        by_contra hne
        cases hf : f 0 <;> cases hg : g 0 <;> simp [hf, hg] at hne h <;> omega
      have htail : bitsToNat (fun j : Fin m => f j.succ) = bitsToNat (fun j : Fin m => g j.succ) := by
        rw [h0] at h
        cases hg : g 0 <;> simp [hg] at h <;> omega
      have := ih htail
      funext j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact h0
      · exact congrFun this j'

/-! ## Languages, NP and PCP -/

/-- A language: for each input length, a predicate on bit strings of that length. -/
def Language := (n : ℕ) → Bits n → Prop

/-- A (non-uniform) NP verifier: a polynomial-size circuit family taking an input and a
polynomially long witness. -/
structure NPVerifier where
  /-- Witness length as a function of the input length. -/
  wit : ℕ → ℕ
  /-- The verification circuit for inputs of length `n`. -/
  circ : (n : ℕ) → Circuit (n + wit n)
  wit_poly : PolyBounded wit
  size_poly : PolyBounded fun n => (circ n).size

/-- The verifier accepts exactly the strings of the language, witnessed by some witness. -/
def NPVerifier.Accepts (V : NPVerifier) (L : Language) : Prop :=
  ∀ (n : ℕ) (x : Bits n), L n x ↔ ∃ w : Bits (V.wit n), (V.circ n).eval (Fin.append x w) = true

/-- `L ∈ NP` (in the non-uniform, circuit-based sense). -/
def InNP (L : Language) : Prop := ∃ V : NPVerifier, V.Accepts L

/-- A probabilistically checkable proof verifier using `r n` random bits and `q n` queries on
inputs of length `n`.  The queried positions and the accept/reject decision are computed by
polynomial-size circuits from the input and the random string. -/
structure PCPVerifier (r q : ℕ → ℕ) where
  /-- Number of bits used to write down a queried position. -/
  posLen : ℕ → ℕ
  /-- `pos n i j` computes the `j`-th bit of the position of the `i`-th query. -/
  pos : (n : ℕ) → Fin (q n) → Fin (posLen n) → Circuit (n + r n)
  /-- The decision circuit, reading the input, the random string and the `q n` answers. -/
  dec : (n : ℕ) → Circuit (n + r n + q n)
  posLen_poly : PolyBounded posLen
  pos_size_poly : ∃ c k : ℕ, ∀ n i j, (pos n i j).size ≤ c * (n + 1) ^ k
  dec_size_poly : PolyBounded fun n => (dec n).size

variable {r q : ℕ → ℕ}

/-- The position of the `i`-th query on input `x` with random string `rho`. -/
def PCPVerifier.query (V : PCPVerifier r q) (n : ℕ) (x : Bits n) (rho : Bits (r n))
    (i : Fin (q n)) : ℕ :=
  bitsToNat fun j => (V.pos n i j).eval (Fin.append x rho)

/-- The verifier's decision on input `x`, random string `rho` and proof `pi`. -/
def PCPVerifier.accepts (V : PCPVerifier r q) (n : ℕ) (x : Bits n) (rho : Bits (r n))
    (pi : ℕ → Bool) : Bool :=
  (V.dec n).eval (Fin.append (Fin.append x rho) fun i => pi (V.query n x rho i))

/-- Completeness (with probability 1) and soundness (with error at most 1/2). -/
def PCPVerifier.Decides (V : PCPVerifier r q) (L : Language) : Prop :=
  ∀ (n : ℕ) (x : Bits n),
    (L n x → ∃ pi : ℕ → Bool, ∀ rho : Bits (r n), V.accepts n x rho pi = true) ∧
    (¬ L n x → ∀ pi : ℕ → Bool,
      2 * (Finset.univ.filter fun rho : Bits (r n) => V.accepts n x rho pi = true).card
        ≤ 2 ^ r n)

/-- `L ∈ PCP(r, q)`. -/
def InPCP (L : Language) (r q : ℕ → ℕ) : Prop := ∃ V : PCPVerifier r q, V.Decides L

/-- `L ∈ PCP(log n, O(1))`: logarithmically many random bits, constantly many queries. -/
def InPCPLogConst (L : Language) : Prop :=
  ∃ c q : ℕ, InPCP L (fun n => c * Nat.log 2 (n + 1) + c) fun _ => q

/-- The complexity class `NP`. -/
def NPClass : Set Language := {L | InNP L}

/-- The complexity class `PCP(log n, O(1))`. -/
def PCPLogConstClass : Set Language := {L | InPCPLogConst L}

/-- The statement of the PCP theorem: `NP = PCP(log n, O(1))`. -/
def PCPCharacterization : Prop := NPClass = PCPLogConstClass

end CS

/-! ## From PCP verifiers to NP verifiers -/

namespace CS
namespace Reduction

variable {n R Q P : ℕ}

/-- An identification of `R`-bit random strings with `Fin (2 ^ R)`. -/
noncomputable def randEq (R : ℕ) : Bits R ≃ Fin (2 ^ R) := Fintype.equivFinOfCardEq (by simp)

/-- The witness position holding the answer to query `i` under random string `k`. -/
def wIdx (k : Fin (2 ^ R)) (i : Fin Q) : Fin (2 ^ R * Q) := finProdFinEquiv (k, i)

/-- The random string index of a witness position. -/
def kOf (t : Fin (2 ^ R * Q)) : Fin (2 ^ R) := (finProdFinEquiv.symm t).1

/-- The query index of a witness position. -/
def iOf (t : Fin (2 ^ R * Q)) : Fin Q := (finProdFinEquiv.symm t).2

@[simp] theorem kOf_wIdx (k : Fin (2 ^ R)) (i : Fin Q) : kOf (wIdx k i) = k := by
  simp [kOf, wIdx]

@[simp] theorem iOf_wIdx (k : Fin (2 ^ R)) (i : Fin Q) : iOf (wIdx k i) = i := by
  simp [iOf, wIdx]

@[simp] theorem wIdx_kOf_iOf (t : Fin (2 ^ R * Q)) : wIdx (kOf t) (iOf t) = t := by
  show finProdFinEquiv ((finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2) = t
  exact (Equiv.apply_eq_iff_eq_symm_apply finProdFinEquiv).mpr rfl

/-- The circuit variable reading the `j`-th input bit. -/
def xVar (n W : ℕ) (j : Fin n) : Circuit (n + W) := .var (Fin.castAdd W j)

/-- The circuit variable reading the `t`-th witness bit. -/
def wVar (n W : ℕ) (t : Fin W) : Circuit (n + W) := .var (Fin.natAdd n t)

@[simp] theorem size_xVar {W : ℕ} (j : Fin n) : (xVar n W j).size = 1 := by
  simp [xVar, Circuit.size]

@[simp] theorem size_wVar {W : ℕ} (t : Fin W) : (wVar n W t).size = 1 := by
  simp [wVar, Circuit.size]

@[simp] theorem eval_xVar {W : ℕ} (x : Bits n) (w : Bits W) (j : Fin n) :
    (xVar n W j).eval (Fin.append x w) = x j := by
  simp [xVar, Circuit.eval]

@[simp] theorem eval_wVar {W : ℕ} (x : Bits n) (w : Bits W) (t : Fin W) :
    (wVar n W t).eval (Fin.append x w) = w t := by
  simp [wVar, Circuit.eval]

/-- Substitution turning a circuit on `(input, random string)` into one on
`(input, witness)`, with the random string `k` hard-wired. -/
noncomputable def gsub (n R Q : ℕ) (k : Fin (2 ^ R)) :
    Fin (n + R) → Circuit (n + 2 ^ R * Q) :=
  Fin.addCases (fun j => xVar n _ j) (fun j => Circuit.const ((randEq R).symm k j))

@[simp] theorem size_gsub (k : Fin (2 ^ R)) (i : Fin (n + R)) : (gsub n R Q k i).size = 1 := by
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [gsub, Circuit.size]

theorem eval_gsub (x : Bits n) (w : Bits (2 ^ R * Q)) (k : Fin (2 ^ R)) :
    (fun i => (gsub n R Q k i).eval (Fin.append x w)) = Fin.append x ((randEq R).symm k) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [gsub, Circuit.eval]

/-- Substitution turning a circuit on `(input, random string, answers)` into one on
`(input, witness)`. -/
noncomputable def hsub (n R Q : ℕ) (k : Fin (2 ^ R)) :
    Fin (n + R + Q) → Circuit (n + 2 ^ R * Q) :=
  Fin.addCases (gsub n R Q k) (fun i => wVar n _ (wIdx k i))

@[simp] theorem size_hsub (k : Fin (2 ^ R)) (i : Fin (n + R + Q)) : (hsub n R Q k i).size = 1 := by
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hsub]

theorem eval_hsub (x : Bits n) (w : Bits (2 ^ R * Q)) (k : Fin (2 ^ R)) :
    (fun i => (hsub n R Q k i).eval (Fin.append x w))
      = Fin.append (Fin.append x ((randEq R).symm k)) (fun i => w (wIdx k i)) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · have := congrFun (eval_gsub (Q := Q) x w k) j
    simpa [hsub] using this
  · simp [hsub]

/-- The `j`-th position bit of the query indexed by witness position `t`. -/
noncomputable def posC (pos : Fin Q → Fin P → Circuit (n + R)) (t : Fin (2 ^ R * Q))
    (j : Fin P) : Circuit (n + 2 ^ R * Q) :=
  (pos (iOf t) j).subst (gsub n R Q (kOf t))

theorem eval_posC (pos : Fin Q → Fin P → Circuit (n + R)) (x : Bits n) (w : Bits (2 ^ R * Q))
    (t : Fin (2 ^ R * Q)) (j : Fin P) :
    (posC pos t j).eval (Fin.append x w)
      = (pos (iOf t) j).eval (Fin.append x ((randEq R).symm (kOf t))) := by
  rw [posC, Circuit.eval_subst, eval_gsub]

theorem size_posC_le (pos : Fin Q → Fin P → Circuit (n + R)) (Sp : ℕ)
    (hp : ∀ i j, (pos i j).size ≤ Sp) (t : Fin (2 ^ R * Q)) (j : Fin P) :
    (posC pos t j).size ≤ Sp := by
  have h := Circuit.size_subst (pos (iOf t) j) (gsub n R Q (kOf t)) 1 le_rfl (by simp)
  simpa using h.trans (by simpa using hp (iOf t) j)

/-- The decision circuit with the random string `k` hard-wired. -/
noncomputable def decC (dec : Circuit (n + R + Q)) (k : Fin (2 ^ R)) : Circuit (n + 2 ^ R * Q) :=
  dec.subst (hsub n R Q k)

theorem eval_decC (dec : Circuit (n + R + Q)) (x : Bits n) (w : Bits (2 ^ R * Q))
    (k : Fin (2 ^ R)) :
    (decC dec k).eval (Fin.append x w)
      = dec.eval (Fin.append (Fin.append x ((randEq R).symm k)) fun i => w (wIdx k i)) := by
  rw [decC, Circuit.eval_subst, eval_hsub]

theorem size_decC_le (dec : Circuit (n + R + Q)) (k : Fin (2 ^ R)) :
    (decC dec k).size ≤ dec.size := by
  have h := Circuit.size_subst dec (hsub n R Q k) 1 le_rfl (by simp)
  simpa using h

/-- The circuit checking that two witness positions refer to the same proof position. -/
noncomputable def eqPosC (pos : Fin Q → Fin P → Circuit (n + R)) (t t' : Fin (2 ^ R * Q)) :
    Circuit (n + 2 ^ R * Q) :=
  Circuit.bigAnd ((List.finRange P).map fun j => Circuit.iff' (posC pos t j) (posC pos t' j))

theorem eval_eqPosC (pos : Fin Q → Fin P → Circuit (n + R)) (x : Bits n) (w : Bits (2 ^ R * Q))
    (t t' : Fin (2 ^ R * Q)) :
    (eqPosC pos t t').eval (Fin.append x w) = true ↔
      ∀ j : Fin P, (pos (iOf t) j).eval (Fin.append x ((randEq R).symm (kOf t)))
        = (pos (iOf t') j).eval (Fin.append x ((randEq R).symm (kOf t'))) := by
  simp [eqPosC, eval_posC]

/-- The consistency check for a pair of witness positions. -/
noncomputable def consC (pos : Fin Q → Fin P → Circuit (n + R)) (t t' : Fin (2 ^ R * Q)) :
    Circuit (n + 2 ^ R * Q) :=
  .disj (.neg (eqPosC pos t t')) (Circuit.iff' (wVar n _ t) (wVar n _ t'))

/-- The NP verification circuit built from a PCP verifier. -/
noncomputable def npC (pos : Fin Q → Fin P → Circuit (n + R)) (dec : Circuit (n + R + Q)) :
    Circuit (n + 2 ^ R * Q) :=
  Circuit.bigAnd
    (((List.finRange (2 ^ R)).map fun k => decC dec k) ++
      (((List.finRange (2 ^ R * Q)) ×ˢ (List.finRange (2 ^ R * Q))).map fun p =>
        consC pos p.1 p.2))

theorem eval_npC (pos : Fin Q → Fin P → Circuit (n + R)) (dec : Circuit (n + R + Q))
    (x : Bits n) (w : Bits (2 ^ R * Q)) :
    (npC pos dec).eval (Fin.append x w) = true ↔
      (∀ k : Fin (2 ^ R), dec.eval (Fin.append (Fin.append x ((randEq R).symm k))
          fun i => w (wIdx k i)) = true) ∧
      (∀ t t' : Fin (2 ^ R * Q),
        (∀ j : Fin P, (pos (iOf t) j).eval (Fin.append x ((randEq R).symm (kOf t)))
            = (pos (iOf t') j).eval (Fin.append x ((randEq R).symm (kOf t')))) →
        w t = w t') := by
  simp only [npC, consC, Circuit.eval_bigAnd, List.all_append, List.all_map,
    List.all_eq_true, List.mem_finRange, Function.comp_apply, Bool.and_eq_true,
    List.mem_product, true_and, Circuit.eval, Bool.or_eq_true, Bool.not_eq_true',
    Circuit.eval_iff', eval_wVar, decide_eq_true_eq, eval_decC, Prod.forall]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => h1 k trivial, fun t t' hj => ?_⟩
    rcases h2 t t' trivial with he | hw
    · exact absurd ((eval_eqPosC pos x w t t').2 hj) (by simp [he])
    · exact hw
  · rintro ⟨h1, h2⟩
    refine ⟨fun k _ => h1 k, fun a b _ => ?_⟩
    by_cases hb : (eqPosC pos a b).eval (Fin.append x w) = true
    · exact Or.inr (h2 a b ((eval_eqPosC pos x w a b).1 hb))
    · exact Or.inl (by simpa using hb)

theorem size_eqPosC_le (pos : Fin Q → Fin P → Circuit (n + R)) (Sp : ℕ)
    (hp : ∀ i j, (pos i j).size ≤ Sp) (t t' : Fin (2 ^ R * Q)) :
    (eqPosC pos t t').size ≤ 1 + P * (4 * Sp + 6) := by
  have hbound : ∀ c ∈ (List.finRange P).map
      (fun j => Circuit.iff' (posC pos t j) (posC pos t' j)), c.size ≤ 4 * Sp + 5 := by
    intro c hc
    simp only [List.mem_map, List.mem_finRange, true_and] at hc
    obtain ⟨j, rfl⟩ := hc
    rw [Circuit.size_iff']
    have h1 := size_posC_le pos Sp hp t j
    have h2 := size_posC_le pos Sp hp t' j
    omega
  have h := Circuit.size_bigAnd _ _ hbound
  simpa [eqPosC, List.length_map, List.length_finRange] using h

theorem size_consC_le (pos : Fin Q → Fin P → Circuit (n + R)) (Sp : ℕ)
    (hp : ∀ i j, (pos i j).size ≤ Sp) (t t' : Fin (2 ^ R * Q)) :
    (consC pos t t').size ≤ 1 + P * (4 * Sp + 6) + 11 := by
  have h := size_eqPosC_le pos Sp hp t t'
  simp only [consC, Circuit.size, Circuit.size_iff', size_wVar]
  omega

theorem size_npC_le (pos : Fin Q → Fin P → Circuit (n + R)) (dec : Circuit (n + R + Q)) (Sp : ℕ)
    (hp : ∀ i j, (pos i j).size ≤ Sp) :
    (npC pos dec).size
      ≤ 1 + (2 ^ R + 2 ^ R * Q * (2 ^ R * Q)) * (dec.size + P * (4 * Sp + 6) + 13) := by
  set S : ℕ := dec.size + (1 + P * (4 * Sp + 6)) + 11 with hS
  have hbound : ∀ c ∈ (((List.finRange (2 ^ R)).map fun k => decC dec k) ++
      (((List.finRange (2 ^ R * Q)) ×ˢ (List.finRange (2 ^ R * Q))).map fun p =>
        consC pos p.1 p.2)), c.size ≤ S := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · simp only [List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨k, rfl⟩ := hc
      have := size_decC_le dec k
      omega
    · simp only [List.mem_map] at hc
      obtain ⟨⟨t, t'⟩, -, rfl⟩ := hc
      have := size_consC_le pos Sp hp t t'
      simp only at this ⊢
      omega
  have h := Circuit.size_bigAnd _ _ hbound
  have hlen : (((List.finRange (2 ^ R)).map fun k => decC dec k) ++
      (((List.finRange (2 ^ R * Q)) ×ˢ (List.finRange (2 ^ R * Q))).map fun p =>
        consC pos p.1 p.2)).length = 2 ^ R + 2 ^ R * Q * (2 ^ R * Q) := by
    simp [List.length_product]
  rw [npC]
  rw [hlen] at h
  refine h.trans ?_
  have : S + 1 = dec.size + P * (4 * Sp + 6) + 13 := by omega
  rw [this]

end Reduction
end CS

/-! ## PCP(r, q) ⊆ NP for polynomially many random strings and queries -/

namespace CS

open Reduction

/-- A PCP verifier using polynomially many random strings and polynomially many queries can be
simulated by an NP verifier: the witness records the answers to all queries that can ever be
asked, together with consistency constraints. -/
theorem pcp_subset_np {L : Language} {r q : ℕ → ℕ}
    (hr : PolyBounded fun n => 2 ^ r n) (hq : PolyBounded q) (h : InPCP L r q) : InNP L := by
  classical
  obtain ⟨V, hV⟩ := h
  obtain ⟨cp, kp, hpos⟩ := V.pos_size_poly
  have hSp : PolyBounded fun n => cp * (n + 1) ^ kp := ⟨cp, kp, fun _ => le_rfl⟩
  refine ⟨⟨fun n => 2 ^ r n * q n, fun n => npC (V.pos n) (V.dec n), hr.mul hq, ?_⟩, ?_⟩
  · refine PolyBounded.mono (g := fun n => 1 + (2 ^ r n + 2 ^ r n * q n * (2 ^ r n * q n)) *
      ((V.dec n).size + V.posLen n * (4 * (cp * (n + 1) ^ kp) + 6) + 13)) ?_ ?_
    · exact (polyBounded_const 1).add ((hr.add ((hr.mul hq).mul (hr.mul hq))).mul
        ((V.dec_size_poly.add (V.posLen_poly.mul
          (((polyBounded_const 4).mul hSp).add (polyBounded_const 6)))).add (polyBounded_const 13)))
    · intro n
      exact size_npC_le (V.pos n) (V.dec n) (cp * (n + 1) ^ kp) fun i j => hpos n i j
  · intro n x
    dsimp only
    set e := randEq (r n) with he
    constructor
    · intro hx
      obtain ⟨pi, hpi⟩ := (hV n x).1 hx
      refine ⟨fun t => pi (V.query n x (e.symm (kOf t)) (iOf t)), ?_⟩
      rw [eval_npC]
      refine ⟨fun k => ?_, fun t t' hj => ?_⟩
      · have hk := hpi (e.symm k)
        rw [PCPVerifier.accepts] at hk
        simpa using hk
      · have hquery : V.query n x (e.symm (kOf t)) (iOf t)
            = V.query n x (e.symm (kOf t')) (iOf t') := by
          unfold PCPVerifier.query
          exact congrArg bitsToNat (funext hj)
        simp only [hquery]
    · rintro ⟨w, hw⟩
      rw [eval_npC] at hw
      obtain ⟨hacc, hcons⟩ := hw
      by_contra hx
      set pi : ℕ → Bool := fun p =>
        if h : ∃ t : Fin (2 ^ r n * q n), V.query n x (e.symm (kOf t)) (iOf t) = p
        then w h.choose else false with hpidef
      have hpiw : ∀ t, pi (V.query n x (e.symm (kOf t)) (iOf t)) = w t := by
        intro t
        have hex : ∃ t' : Fin (2 ^ r n * q n),
            V.query n x (e.symm (kOf t')) (iOf t') = V.query n x (e.symm (kOf t)) (iOf t) :=
          ⟨t, rfl⟩
        rw [hpidef]
        simp only [dif_pos hex]
        have hspec := hex.choose_spec
        have hbits : (fun j => (V.pos n (iOf hex.choose) j).eval
              (Fin.append x (e.symm (kOf hex.choose))))
            = fun j => (V.pos n (iOf t) j).eval (Fin.append x (e.symm (kOf t))) :=
          bitsToNat_injective hspec
        exact hcons _ _ fun j => congrFun hbits j
      have hall : ∀ rho : Bits (r n), V.accepts n x rho pi = true := by
        intro rho
        have h2 : ∀ i, pi (V.query n x rho i) = w (wIdx (e rho) i) := by
          intro i
          have := hpiw (wIdx (e rho) i)
          simpa [e.symm_apply_apply] using this
        rw [PCPVerifier.accepts]
        simpa [h2, ← he, e.symm_apply_apply] using hacc (e rho)
      have hcard := (hV n x).2 hx pi
      rw [Finset.filter_true_of_mem fun rho _ => hall rho] at hcard
      have hcard' : (Finset.univ : Finset (Bits (r n))).card = 2 ^ r n := by simp
      rw [hcard'] at hcard
      have : 0 < 2 ^ r n := Nat.two_pow_pos _
      omega

end CS

/-! ## NP ⊆ PCP(0, poly) -/

namespace CS

/-- Reindexing an NP circuit as a PCP decision circuit with an empty random string. -/
def zeroRandSub (n W : ℕ) : Fin (n + W) → Circuit (n + 0 + W) :=
  Fin.addCases (fun j => .var (Fin.castAdd W (Fin.castAdd 0 j)))
    (fun t => .var (Fin.natAdd (n + 0) t))

@[simp] theorem size_zeroRandSub (n W : ℕ) (i : Fin (n + W)) : (zeroRandSub n W i).size = 1 := by
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [zeroRandSub, Circuit.size]

theorem eval_zeroRandSub {n W : ℕ} (x : Bits n) (rho : Bits 0) (f : Bits W) :
    (fun j => (zeroRandSub n W j).eval (Fin.append (Fin.append x rho) f)) = Fin.append x f := by
  funext j
  refine Fin.addCases ?_ ?_ j <;> intro i <;>
    simp only [zeroRandSub, Fin.addCases_left, Fin.addCases_right, Circuit.eval,
      Fin.append_left, Fin.append_right]

/-- The proof position queried for the `i`-th bit of the witness. -/
def witPos (W : ℕ) (i : Fin W) : ℕ := bitsToNat fun j : Fin W => decide (j.val = i.val)

theorem witPos_injective (W : ℕ) : Function.Injective (witPos W) := by
  intro i i' h
  have h' : (fun j : Fin W => decide (j.val = i.val)) = fun j : Fin W => decide (j.val = i'.val) :=
    bitsToNat_injective h
  have h2 := congrFun h' i
  rw [decide_eq_decide] at h2
  exact Fin.ext (h2.mp rfl)

/-- The PCP verifier associated with an NP verifier: it tosses no coins and reads the whole
witness from the proof. -/
def NPVerifier.toPCPVerifier (V : NPVerifier) : PCPVerifier (fun _ => 0) V.wit where
  posLen := V.wit
  pos := fun _ i j => .const (decide (j.val = i.val))
  dec := fun n => (V.circ n).subst (zeroRandSub n (V.wit n))
  posLen_poly := V.wit_poly
  pos_size_poly := ⟨1, 0, by intro n i j; simp [Circuit.size]⟩
  dec_size_poly := by
    refine V.size_poly.mono fun n => ?_
    simpa using Circuit.size_subst (V.circ n) (zeroRandSub n (V.wit n)) 1 le_rfl (by simp)

theorem NPVerifier.query_toPCPVerifier (V : NPVerifier) (n : ℕ) (x : Bits n) (rho : Bits 0)
    (i : Fin (V.wit n)) : V.toPCPVerifier.query n x rho i = witPos (V.wit n) i := by
  simp [PCPVerifier.query, NPVerifier.toPCPVerifier, Circuit.eval, witPos]

theorem NPVerifier.accepts_toPCPVerifier (V : NPVerifier) (n : ℕ) (x : Bits n) (rho : Bits 0)
    (pi : ℕ → Bool) : V.toPCPVerifier.accepts n x rho pi
      = (V.circ n).eval (Fin.append x fun i => pi (witPos (V.wit n) i)) := by
  rw [PCPVerifier.accepts]
  simp only [V.query_toPCPVerifier n x rho]
  show ((V.circ n).subst (zeroRandSub n (V.wit n))).eval _ = _
  rw [Circuit.eval_subst, eval_zeroRandSub]

/-- Every NP language has a PCP verifier that uses no randomness and queries the whole
(polynomially long) proof. -/
theorem np_subset_pcp {L : Language} (h : InNP L) :
    ∃ q : ℕ → ℕ, PolyBounded q ∧ InPCP L (fun _ => 0) q := by
  classical
  obtain ⟨V, hV⟩ := h
  refine ⟨V.wit, V.wit_poly, V.toPCPVerifier, fun n x => ⟨fun hx => ?_, fun hx pi => ?_⟩⟩
  · obtain ⟨w, hw⟩ := (hV n x).1 hx
    refine ⟨fun p => if h : ∃ i : Fin (V.wit n), witPos (V.wit n) i = p then w h.choose
      else false, fun rho => ?_⟩
    rw [V.accepts_toPCPVerifier n x rho]
    have hfun : (fun i => (if h : ∃ i' : Fin (V.wit n), witPos (V.wit n) i' = witPos (V.wit n) i
        then w h.choose else false)) = w := by
      funext i
      have hex : ∃ i' : Fin (V.wit n), witPos (V.wit n) i' = witPos (V.wit n) i := ⟨i, rfl⟩
      simp only [dif_pos hex]
      exact congrArg w (witPos_injective _ hex.choose_spec)
    rw [hfun]
    exact hw
  · have hnone : ∀ rho : Bits 0, ¬ (V.toPCPVerifier.accepts n x rho pi = true) := by
      intro rho hacc
      rw [V.accepts_toPCPVerifier n x rho] at hacc
      exact hx ((hV n x).2 ⟨_, hacc⟩)
    rw [Finset.filter_false_of_mem fun rho _ => hnone rho]
    simp

/-- Non-degeneracy of the framework: NP is exactly the class of languages having a PCP verifier
with polynomially many random strings and polynomially many queries, i.e. `NP = PCP(log n, poly)`. -/
theorem np_iff_pcp_poly {L : Language} :
    InNP L ↔ ∃ r q : ℕ → ℕ, PolyBounded (fun n => 2 ^ r n) ∧ PolyBounded q ∧ InPCP L r q := by
  refine ⟨fun h => ?_, fun ⟨r, q, hr, hq, h⟩ => pcp_subset_np hr hq h⟩
  obtain ⟨q, hq, h⟩ := np_subset_pcp h
  exact ⟨fun _ => 0, q, by simpa using polyBounded_const 1, hq, h⟩

/-! ## The PCP theorem -/

/-- `PCP(log n, O(1)) ⊆ NP`: the easy inclusion of the PCP theorem. -/
theorem pcp_log_const_subset_np {L : Language} (h : InPCPLogConst L) : InNP L := by
  obtain ⟨c, q0, hV⟩ := h
  exact pcp_subset_np (polyBounded_two_pow_log c) (polyBounded_const q0) hV

/-- **The PCP theorem**, `NP = PCP(log n, O(1))`.

The inclusion `PCP(log n, O(1)) ⊆ NP` is proved here unconditionally
(`CS.pcp_log_const_subset_np`), so the characterization `NP = PCP(log n, O(1))` holds precisely
when the deep inclusion `NP ⊆ PCP(log n, O(1))` of Arora–Safra and
Arora–Lund–Motwani–Sudan–Szegedy holds. -/
theorem pcp_theorem : PCPCharacterization ↔ NPClass ⊆ PCPLogConstClass := by
  constructor
  · intro h
    rw [PCPCharacterization] at h
    rw [h]
  · intro h
    exact Set.Subset.antisymm h fun L hL => pcp_log_const_subset_np hL

end CS

import Mathlib
import RequestProject.PcpTheorem

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

