import Mathlib
import RequestProject.Circuits

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

/-!
## Overview

This file formalises the statement `NP = PCP(log n, O(1))` (the PCP theorem) in the
non-uniform (Boolean circuit) model of efficient computation, and proves the "easy"
inclusion `PCP(log n, O(1)) ⊆ NP` in full.

*  A language is a predicate on bit strings (`CS.Language`).
*  `CS.InNP L` says that `L` has a polynomial-length witness that is checked by a
   polynomial-size Boolean circuit.
*  `CS.InPCP L` says that `L` has a probabilistically checkable proof system with
   `O(log n)` random bits, a constant number `q` of queries, perfect completeness and
   soundness error at most `1/2`; the query positions and the decision predicate are
   computed by polynomial-size circuits.

`CS.pcp_subset_np` proves `PCP(log n, O(1)) ⊆ NP` unconditionally: a witness for the NP
system is the table of answers of the PCP verifier on all `2^{O(log n)} = poly(n)` random
strings, together with the consistency requirement that two queries landing on the same
proof position receive the same answer.

Proof positions are named by bit strings of length `pbits n` with `pbits` polynomially
bounded; since the verifier only ever inspects `2 ^ rlen n * q = poly(n)` positions, no
further restriction on the proof length is needed.

The reverse inclusion `NP ⊆ PCP(log n, O(1))` is the deep content of the PCP theorem
(Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy); it is *not* proved here, and appears as
an explicit hypothesis `hard` of `CS.pcp_theorem`.
-/

namespace CS

/-- A language: a set of finite bit strings. -/
abbrev Language := List Bool → Prop

/-- The variable assignment described by a bit string (out-of-range variables are `false`). -/
def asFun (l : List Bool) : ℕ → Bool := fun i => l.getD i false

lemma asFun_apply (l : List Bool) (i : ℕ) : asFun l i = l.getD i false := rfl

lemma asFun_append_left (x y : List Bool) {t : ℕ} (h : t < x.length) :
    asFun (x ++ y) t = asFun x t := List.getD_append _ _ _ _ h

lemma asFun_append_right (x y : List Bool) {t : ℕ} (h : x.length ≤ t) :
    asFun (x ++ y) t = asFun y (t - x.length) := List.getD_append_right _ _ _ _ h

lemma asFun_append_add (x y : List Bool) (m : ℕ) : asFun (x ++ y) (x.length + m) = asFun y m := by
  rw [asFun_append_right _ _ (by omega)]
  congr 1
  omega

lemma asFun_of_length_le {l : List Bool} {t : ℕ} (h : l.length ≤ t) : asFun l t = false :=
  List.getD_eq_default _ _ h

lemma getD_map_range (f : ℕ → Bool) {m j : ℕ} (hj : j < m) :
    ((List.range m).map f).getD j false = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

/-! ## The class NP (non-uniform version: polynomial-size verifier circuits) -/

/-- A non-uniform NP verifier: for inputs of length `n` a witness of length `wlen n` is
checked by the circuit `circ n` on the concatenation of input and witness.  Both the
witness length and the circuit size are polynomially bounded. -/
structure NPVerifier where
  wlen : ℕ → ℕ
  circ : ℕ → Circ
  wlen_poly : IsPoly wlen
  size_poly : IsPoly fun n => (circ n).size

/-- The verifier accepts input `x` with witness `w`. -/
def NPVerifier.Accepts (S : NPVerifier) (x w : List Bool) : Prop :=
  (S.circ x.length).eval (asFun (x ++ w)) = true

/-- `L ∈ NP`. -/
def InNP (L : Language) : Prop :=
  ∃ S : NPVerifier, ∀ x : List Bool,
    L x ↔ ∃ w : List Bool, w.length = S.wlen x.length ∧ S.Accepts x w

/-! ## The class PCP(log n, O(1)) -/

/-- A probabilistically checkable proof verifier with logarithmic randomness and a
constant number of queries.

On input `x` of length `n` the verifier tosses `rlen n` coins (`2 ^ rlen n` is polynomially
bounded, i.e. `rlen n = O(log n)`), and makes `q` non-adaptive queries to a proof.  Proof
positions are named by bit strings of length `pbits n`; the `b`-th bit of the position of
the `j`-th query is computed by the circuit `posCirc n j b` from the input and the random
string.  The circuit `accCirc n` decides acceptance from the input, the random string and
the `q` answers.  All circuits have polynomial size. -/
structure PCPVerifier where
  q : ℕ
  rlen : ℕ → ℕ
  pbits : ℕ → ℕ
  posCirc : ℕ → ℕ → ℕ → Circ
  accCirc : ℕ → Circ
  rand_log : IsPoly fun n => 2 ^ rlen n
  pbits_poly : IsPoly pbits
  pos_size_poly : ∃ c k : ℕ, ∀ n j b, (posCirc n j b).size ≤ c * (n + 1) ^ k
  acc_size_poly : IsPoly fun n => (accCirc n).size

namespace PCPVerifier

variable (V : PCPVerifier)

/-- The name (a bit string of length `pbits n`) of the position queried by the `j`-th query
on input `x` and random string `r`. -/
def position (x r : List Bool) (j : ℕ) : List Bool :=
  (List.range (V.pbits x.length)).map fun b => (V.posCirc x.length j b).eval (asFun (x ++ r))

/-- The list of answers received from the proof `pi`. -/
def answers (x r : List Bool) (pi : List Bool → Bool) : List Bool :=
  (List.range V.q).map fun j => pi (V.position x r j)

/-- The verifier's decision given the input, the random string and the list of answers. -/
def accWith (x r ans : List Bool) : Bool :=
  (V.accCirc x.length).eval (asFun (x ++ r ++ ans))

/-- The verifier's decision on input `x`, random string `r` and proof `pi`. -/
def acc (x r : List Bool) (pi : List Bool → Bool) : Bool :=
  V.accWith x r (V.answers x r pi)

/-- The verifier accepts. -/
def Accepts (x r : List Bool) (pi : List Bool → Bool) : Prop := V.acc x r pi = true

/-- The number of random strings on which the verifier accepts. -/
def acceptCount (x : List Bool) (pi : List Bool → Bool) : ℕ :=
  ((allBits (V.rlen x.length)).filter fun r => V.acc x r pi).length

end PCPVerifier

/-- `L ∈ PCP(log n, O(1))`: there is a PCP verifier with logarithmic randomness and a
constant number of queries which accepts some proof with probability `1` for every
`x ∈ L`, and accepts every proof with probability at most `1/2` for every `x ∉ L`. -/
def InPCP (L : Language) : Prop :=
  ∃ V : PCPVerifier,
    (∀ x : List Bool, L x → ∃ pi : List Bool → Bool,
        ∀ r ∈ allBits (V.rlen x.length), V.Accepts x r pi) ∧
    (∀ x : List Bool, ¬ L x → ∀ pi : List Bool → Bool,
        2 * V.acceptCount x pi ≤ 2 ^ V.rlen x.length)

/-! ## Bookkeeping lists -/

/-- The `i`-th random string of length `V.rlen n`. -/
def rstr (V : PCPVerifier) (n i : ℕ) : List Bool := (allBits (V.rlen n)).getD i []

lemma length_rstr {V : PCPVerifier} {n i : ℕ} (hi : i < 2 ^ V.rlen n) :
    (rstr V n i).length = V.rlen n := by
  have hlt : i < (allBits (V.rlen n)).length := by simpa using hi
  have : rstr V n i = (allBits (V.rlen n))[i] := List.getD_eq_getElem _ _ hlt
  rw [this]
  exact mem_allBits.1 (List.getElem_mem hlt)

lemma exists_index_rstr {V : PCPVerifier} {n : ℕ} {r : List Bool}
    (hr : r ∈ allBits (V.rlen n)) : ∃ i < 2 ^ V.rlen n, rstr V n i = r := by
  obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.1 hr
  refine ⟨i, by simpa using hi, ?_⟩
  rw [rstr, List.getD_eq_getElem _ _ hi, hval]

/-- The list of index pairs `(i, j)` with `i < R`, `j < q`. -/
def pairsList (R q : ℕ) : List (ℕ × ℕ) :=
  (List.range R).flatMap fun i => (List.range q).map fun j => (i, j)

@[simp] lemma mem_pairsList {R q i j : ℕ} : (i, j) ∈ pairsList R q ↔ i < R ∧ j < q := by
  simp [pairsList]

@[simp] lemma length_pairsList (R q : ℕ) : (pairsList R q).length = R * q := by
  simp [pairsList, List.length_flatMap]

/-- The answer table of the witness `w` for the `i`-th random string. -/
def ansOf (V : PCPVerifier) (w : List Bool) (i : ℕ) : List Bool :=
  (List.range V.q).map fun j => w.getD (i * V.q + j) false

/-- The witness list encoding an answer table `a`. -/
def tableList (q R : ℕ) (a : ℕ → ℕ → Bool) : List Bool :=
  (List.range (R * q)).map fun m => a (m / q) (m % q)

@[simp] lemma length_tableList (q R : ℕ) (a : ℕ → ℕ → Bool) :
    (tableList q R a).length = R * q := by simp [tableList]

lemma tableList_getD {q R i j : ℕ} {a : ℕ → ℕ → Bool} (hi : i < R) (hj : j < q) :
    (tableList q R a).getD (i * q + j) false = a i j := by
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hlt : i * q + j < R * q := by
    have : (i + 1) * q ≤ R * q := Nat.mul_le_mul_right _ hi
    have h2 : i * q + j < (i + 1) * q := by
      have : (i + 1) * q = i * q + q := by ring
      omega
    omega
  have hlen : i * q + j < (tableList q R a).length := by simpa using hlt
  rw [List.getD_eq_getElem _ _ hlen]
  have hcomm : i * q + j = j + q * i := by ring
  have hdiv : (i * q + j) / q = i := by
    rw [hcomm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * q + j) % q = j := by
    rw [hcomm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp [tableList, hdiv, hmod]

/-! ## The circuits simulating a PCP verifier -/

/-- Substitution used to evaluate a position circuit: input variables stay, random bits are
hard-wired to the `i`-th random string. -/
def sigmaPos (V : PCPVerifier) (n i : ℕ) : ℕ → Circ := fun t =>
  if t < n then Circ.var t else Circ.cst ((rstr V n i).getD (t - n) false)

/-- Substitution used to evaluate the decision circuit: input variables stay, random bits
are hard-wired to the `i`-th random string, and the answers are read off the witness. -/
def sigmaAcc (V : PCPVerifier) (n i : ℕ) : ℕ → Circ := fun t =>
  if t < n then Circ.var t
  else if t < n + V.rlen n then Circ.cst ((rstr V n i).getD (t - n) false)
  else if t < n + V.rlen n + V.q then Circ.var (n + i * V.q + (t - n - V.rlen n))
  else Circ.cst false

/-- Circuit computing the `b`-th bit of the position of query `j` under randomness `i`. -/
def posBitCirc (V : PCPVerifier) (n i j b : ℕ) : Circ :=
  (V.posCirc n j b).comp (sigmaPos V n i)

/-- Circuit testing that queries `(i, j)` and `(i', j')` address the same proof position. -/
def posEqCirc (V : PCPVerifier) (n i j i' j' : ℕ) : Circ :=
  Circ.bigAnd ((List.range (V.pbits n)).map fun b =>
    Circ.xnor (posBitCirc V n i j b) (posBitCirc V n i' j' b))

/-- Consistency constraint: equal positions must get equal answers. -/
def consCheckCirc (V : PCPVerifier) (n i j i' j' : ℕ) : Circ :=
  Circ.impl (posEqCirc V n i j i' j')
    (Circ.xnor (Circ.var (n + i * V.q + j)) (Circ.var (n + i' * V.q + j')))

/-- The acceptance constraint for the `i`-th random string. -/
def accCheckCirc (V : PCPVerifier) (n i : ℕ) : Circ := (V.accCirc n).comp (sigmaAcc V n i)

/-- The list of all consistency constraints. -/
def consList (V : PCPVerifier) (n : ℕ) : List Circ :=
  (pairsList (2 ^ V.rlen n) V.q).flatMap fun p =>
    (pairsList (2 ^ V.rlen n) V.q).map fun p' => consCheckCirc V n p.1 p.2 p'.1 p'.2

/-- The NP verification circuit simulating the PCP verifier. -/
def npCirc (V : PCPVerifier) (n : ℕ) : Circ :=
  Circ.bigAnd (((List.range (2 ^ V.rlen n)).map fun i => accCheckCirc V n i) ++ consList V n)

/-! ## Semantics of the simulating circuits -/

lemma sigmaPos_eval (V : PCPVerifier) (x w : List Bool) (i : ℕ) :
    (fun t => (sigmaPos V x.length i t).eval (asFun (x ++ w)))
      = asFun (x ++ rstr V x.length i) := by
  funext t
  by_cases ht : t < x.length
  · simp only [sigmaPos, if_pos ht, Circ.eval_var]
    rw [asFun_append_left _ _ ht, asFun_append_left _ _ ht]
  · have ht' : x.length ≤ t := Nat.le_of_not_lt ht
    simp only [sigmaPos, if_neg ht, Circ.eval_cst]
    rw [asFun_append_right _ _ ht', asFun_apply]

lemma posBitCirc_eval (V : PCPVerifier) (x w : List Bool) (i j b : ℕ) :
    (posBitCirc V x.length i j b).eval (asFun (x ++ w))
      = (V.posCirc x.length j b).eval (asFun (x ++ rstr V x.length i)) := by
  rw [posBitCirc, Circ.eval_comp, sigmaPos_eval]

lemma posEqCirc_eval (V : PCPVerifier) (x w : List Bool) (i j i' j' : ℕ) :
    ((posEqCirc V x.length i j i' j').eval (asFun (x ++ w)) = true)
      ↔ V.position x (rstr V x.length i) j = V.position x (rstr V x.length i') j' := by
  rw [posEqCirc]
  rw [Circ.eval_bigAnd]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    PCPVerifier.position]
  constructor
  · intro h
    refine List.map_inj_left.2 ?_
    intro b hb
    have hb' : b < V.pbits x.length := by simpa using hb
    have := h _ b hb' rfl
    rw [Circ.eval_xnor] at this
    rw [posBitCirc_eval, posBitCirc_eval] at this
    exact this
  · intro h c b hb hc
    subst hc
    rw [Circ.eval_xnor, posBitCirc_eval, posBitCirc_eval]
    have := List.map_inj_left.1 h b (by simpa using hb)
    exact this

lemma sigmaAcc_eval (V : PCPVerifier) (x w : List Bool) (i : ℕ)
    (hi : i < 2 ^ V.rlen x.length) :
    (fun t => (sigmaAcc V x.length i t).eval (asFun (x ++ w)))
      = asFun (x ++ rstr V x.length i ++ ansOf V w i) := by
  have hrlen : (rstr V x.length i).length = V.rlen x.length := length_rstr hi
  have hanslen : (ansOf V w i).length = V.q := by simp [ansOf]
  have hxr : (x ++ rstr V x.length i).length = x.length + V.rlen x.length := by
    rw [List.length_append, hrlen]
  funext t
  simp only [sigmaAcc]
  by_cases ht : t < x.length
  · rw [if_pos ht, Circ.eval_var, asFun_append_left x w ht,
      asFun_append_left _ (ansOf V w i) (by rw [hxr]; omega),
      asFun_append_left x _ ht]
  · rw [if_neg ht]
    by_cases ht2 : t < x.length + V.rlen x.length
    · rw [if_pos ht2, Circ.eval_cst,
        asFun_append_left _ (ansOf V w i) (by rw [hxr]; omega),
        asFun_append_right x _ (by omega), asFun_apply]
    · rw [if_neg ht2]
      by_cases ht3 : t < x.length + V.rlen x.length + V.q
      · have hj : t - x.length - V.rlen x.length < V.q := by omega
        rw [if_pos ht3, Circ.eval_var,
          show x.length + i * V.q + (t - x.length - V.rlen x.length)
              = x.length + (i * V.q + (t - x.length - V.rlen x.length)) by ring,
          asFun_append_add x w,
          asFun_append_right _ (ansOf V w i) (by rw [hxr]; omega), hxr, asFun_apply,
          show t - (x.length + V.rlen x.length) = t - x.length - V.rlen x.length by omega,
          ansOf, asFun_apply, getD_map_range _ hj]
      · rw [if_neg ht3, Circ.eval_cst]
        refine (asFun_of_length_le ?_).symm
        rw [List.length_append, hxr, hanslen]
        omega

lemma accCheckCirc_eval (V : PCPVerifier) (x w : List Bool) (i : ℕ)
    (hi : i < 2 ^ V.rlen x.length) :
    (accCheckCirc V x.length i).eval (asFun (x ++ w))
      = V.accWith x (rstr V x.length i) (ansOf V w i) := by
  rw [accCheckCirc, Circ.eval_comp, sigmaAcc_eval V x w i hi, PCPVerifier.accWith]

/-- The main semantic property of the simulating circuit. -/
lemma npCirc_eval_iff (V : PCPVerifier) (x w : List Bool) :
    ((npCirc V x.length).eval (asFun (x ++ w)) = true) ↔
      ((∀ i < 2 ^ V.rlen x.length, V.accWith x (rstr V x.length i) (ansOf V w i) = true) ∧
        (∀ i < 2 ^ V.rlen x.length, ∀ j < V.q, ∀ i' < 2 ^ V.rlen x.length, ∀ j' < V.q,
          V.position x (rstr V x.length i) j = V.position x (rstr V x.length i') j' →
            w.getD (i * V.q + j) false = w.getD (i' * V.q + j') false)) := by
  rw [npCirc, Circ.eval_bigAnd]
  constructor
  · intro h
    constructor
    · intro i hi
      have hmem : accCheckCirc V x.length i ∈
          (((List.range (2 ^ V.rlen x.length)).map fun i => accCheckCirc V x.length i)
            ++ consList V x.length) := by
        apply List.mem_append_left
        exact List.mem_map_of_mem (by simpa using hi)
      have := h _ hmem
      rwa [accCheckCirc_eval V x w i hi] at this
    · intro i hi j hj i' hi' j' hj' hpos
      have hmem : consCheckCirc V x.length i j i' j' ∈
          (((List.range (2 ^ V.rlen x.length)).map fun i => accCheckCirc V x.length i)
            ++ consList V x.length) := by
        apply List.mem_append_right
        rw [consList, List.mem_flatMap]
        exact ⟨(i, j), mem_pairsList.2 ⟨hi, hj⟩,
          List.mem_map_of_mem (mem_pairsList.2 ⟨hi', hj'⟩)⟩
      have hc := h _ hmem
      rw [consCheckCirc, Circ.eval_impl] at hc
      have h1 : (posEqCirc V x.length i j i' j').eval (asFun (x ++ w)) = true :=
        (posEqCirc_eval V x w i j i' j').2 hpos
      have h2 := hc h1
      rw [Circ.eval_xnor, Circ.eval_var, Circ.eval_var,
        show x.length + i * V.q + j = x.length + (i * V.q + j) by ring,
        show x.length + i' * V.q + j' = x.length + (i' * V.q + j') by ring,
        asFun_append_add x w, asFun_append_add x w, asFun_apply, asFun_apply] at h2
      exact h2
  · rintro ⟨hacc, hcons⟩ c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · rw [List.mem_map] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      have hi' : i < 2 ^ V.rlen x.length := by simpa using hi
      rw [accCheckCirc_eval V x w i hi']
      exact hacc i hi'
    · rw [consList, List.mem_flatMap] at hc
      obtain ⟨p, hp, hc⟩ := hc
      rw [List.mem_map] at hc
      obtain ⟨p', hp', rfl⟩ := hc
      obtain ⟨hi, hj⟩ := mem_pairsList.1 (show (p.1, p.2) ∈ _ by simpa using hp)
      obtain ⟨hi', hj'⟩ := mem_pairsList.1 (show (p'.1, p'.2) ∈ _ by simpa using hp')
      rw [consCheckCirc, Circ.eval_impl]
      intro heq
      rw [Circ.eval_xnor]
      have hpos := (posEqCirc_eval V x w p.1 p.2 p'.1 p'.2).1 heq
      have hval := hcons p.1 hi p.2 hj p'.1 hi' p'.2 hj' hpos
      rw [Circ.eval_var, Circ.eval_var,
        show x.length + p.1 * V.q + p.2 = x.length + (p.1 * V.q + p.2) by ring,
        show x.length + p'.1 * V.q + p'.2 = x.length + (p'.1 * V.q + p'.2) by ring,
        asFun_append_add x w, asFun_append_add x w, asFun_apply, asFun_apply]
      exact hval

/-! ## Size bounds -/

/-- An explicit polynomial bound for the size of the simulating circuit. -/
def npSizeBound (V : PCPVerifier) (c k : ℕ) (n : ℕ) : ℕ :=
  (2 ^ V.rlen n + (2 ^ V.rlen n * V.q) * (2 ^ V.rlen n * V.q)) *
    ((2 * (V.accCirc n).size + V.pbits n * (8 * (c * (n + 1) ^ k) + 6) + 12) + 1) + 1

lemma size_posBitCirc_le (V : PCPVerifier) {c k : ℕ}
    (hpos : ∀ n j b, (V.posCirc n j b).size ≤ c * (n + 1) ^ k) (n i j b : ℕ) :
    (posBitCirc V n i j b).size ≤ 2 * (c * (n + 1) ^ k) := by
  have hs : ∀ t, (sigmaPos V n i t).size ≤ 1 := by
    intro t
    by_cases ht : t < n <;> simp [sigmaPos, ht, Circ.size]
  have := Circ.size_comp_le (V.posCirc n j b) (sigmaPos V n i) 1 hs
  calc (posBitCirc V n i j b).size ≤ (V.posCirc n j b).size * 2 := by
        simpa [posBitCirc] using this
    _ ≤ (c * (n + 1) ^ k) * 2 := Nat.mul_le_mul_right _ (hpos n j b)
    _ = 2 * (c * (n + 1) ^ k) := by ring

lemma size_consCheckCirc_le (V : PCPVerifier) {c k : ℕ}
    (hpos : ∀ n j b, (V.posCirc n j b).size ≤ c * (n + 1) ^ k) (n i j i' j' : ℕ) :
    (consCheckCirc V n i j i' j').size ≤ V.pbits n * (8 * (c * (n + 1) ^ k) + 6) + 12 := by
  set P := c * (n + 1) ^ k with hP
  have hxnor : ∀ d ∈ (List.range (V.pbits n)).map (fun b =>
      Circ.xnor (posBitCirc V n i j b) (posBitCirc V n i' j' b)), d.size ≤ 8 * P + 5 := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨b, _, rfl⟩ := hd
    rw [Circ.size_xnor]
    have h1 := size_posBitCirc_le V hpos n i j b
    have h2 := size_posBitCirc_le V hpos n i' j' b
    omega
  have hbig := Circ.size_bigAnd_le _ (8 * P + 5) hxnor
  rw [List.length_map, List.length_range] at hbig
  rw [consCheckCirc, Circ.size_impl, Circ.size_xnor]
  simp only [Circ.size]
  have : (posEqCirc V n i j i' j').size ≤ V.pbits n * (8 * P + 6) + 1 := by
    simpa [posEqCirc] using hbig
  omega

lemma size_accCheckCirc_le (V : PCPVerifier) (n i : ℕ) :
    (accCheckCirc V n i).size ≤ 2 * (V.accCirc n).size := by
  have hs : ∀ t, (sigmaAcc V n i t).size ≤ 1 := by
    intro t
    by_cases h1 : t < n
    · simp [sigmaAcc, h1, Circ.size]
    · by_cases h2 : t < n + V.rlen n
      · simp [sigmaAcc, h1, h2, Circ.size]
      · by_cases h3 : t < n + V.rlen n + V.q <;> simp [sigmaAcc, h1, h2, h3, Circ.size]
  have := Circ.size_comp_le (V.accCirc n) (sigmaAcc V n i) 1 hs
  calc (accCheckCirc V n i).size ≤ (V.accCirc n).size * 2 := by simpa [accCheckCirc] using this
    _ = 2 * (V.accCirc n).size := by ring

lemma size_npCirc_le (V : PCPVerifier) {c k : ℕ}
    (hpos : ∀ n j b, (V.posCirc n j b).size ≤ c * (n + 1) ^ k) (n : ℕ) :
    (npCirc V n).size ≤ npSizeBound V c k n := by
  set B := 2 * (V.accCirc n).size + V.pbits n * (8 * (c * (n + 1) ^ k) + 6) + 12 with hB
  have hbound : ∀ d ∈ (((List.range (2 ^ V.rlen n)).map fun i => accCheckCirc V n i)
      ++ consList V n), d.size ≤ B := by
    intro d hd
    rw [List.mem_append] at hd
    rcases hd with hd | hd
    · rw [List.mem_map] at hd
      obtain ⟨i, _, rfl⟩ := hd
      have := size_accCheckCirc_le V n i
      omega
    · rw [consList, List.mem_flatMap] at hd
      obtain ⟨p, _, hd⟩ := hd
      rw [List.mem_map] at hd
      obtain ⟨p', _, rfl⟩ := hd
      have := size_consCheckCirc_le V hpos n p.1 p.2 p'.1 p'.2
      omega
  have hlen : (((List.range (2 ^ V.rlen n)).map fun i => accCheckCirc V n i)
      ++ consList V n).length
      = 2 ^ V.rlen n + (2 ^ V.rlen n * V.q) * (2 ^ V.rlen n * V.q) := by
    simp [consList, List.length_flatMap]
  have := Circ.size_bigAnd_le _ B hbound
  rw [hlen] at this
  simpa [npCirc, npSizeBound, hB] using this

lemma isPoly_npSizeBound (V : PCPVerifier) (c k : ℕ) : IsPoly (npSizeBound V c k) := by
  have hR : IsPoly fun n => 2 ^ V.rlen n := V.rand_log
  have hq : IsPoly fun _ : ℕ => V.q := isPoly_const _
  have hA : IsPoly fun n => (V.accCirc n).size := V.acc_size_poly
  have hP : IsPoly fun n => V.pbits n := V.pbits_poly
  have hc : IsPoly fun n => c * (n + 1) ^ k := ⟨c, k, fun _ => le_refl _⟩
  have h1 : IsPoly fun n => 2 ^ V.rlen n * V.q := hR.mul hq
  have h2 : IsPoly fun n => (2 ^ V.rlen n * V.q) * (2 ^ V.rlen n * V.q) := h1.mul h1
  have h3 : IsPoly fun n => 2 ^ V.rlen n + (2 ^ V.rlen n * V.q) * (2 ^ V.rlen n * V.q) :=
    hR.add h2
  have h4 : IsPoly fun n => 2 * (V.accCirc n).size := (isPoly_const 2).mul hA
  have h5 : IsPoly fun n => V.pbits n * (8 * (c * (n + 1) ^ k) + 6) :=
    hP.mul (((isPoly_const 8).mul hc).add (isPoly_const 6))
  have h6 : IsPoly fun n =>
      (2 * (V.accCirc n).size + V.pbits n * (8 * (c * (n + 1) ^ k) + 6) + 12) + 1 :=
    ((h4.add h5).add (isPoly_const 12)).add (isPoly_const 1)
  exact (h3.mul h6).add (isPoly_const 1)

/-! ## The easy inclusion: PCP(log n, O(1)) ⊆ NP -/

/-- The proof function reconstructed from a consistent answer table. -/
def proofOf (V : PCPVerifier) (x w : List Bool) : List Bool → Bool := fun p =>
  match (pairsList (2 ^ V.rlen x.length) V.q).find?
      (fun ij => V.position x (rstr V x.length ij.1) ij.2 == p) with
  | some ij => w.getD (ij.1 * V.q + ij.2) false
  | none => false

lemma proofOf_apply (V : PCPVerifier) (x w : List Bool)
    (hcons : ∀ i < 2 ^ V.rlen x.length, ∀ j < V.q, ∀ i' < 2 ^ V.rlen x.length, ∀ j' < V.q,
      V.position x (rstr V x.length i) j = V.position x (rstr V x.length i') j' →
        w.getD (i * V.q + j) false = w.getD (i' * V.q + j') false)
    {i j : ℕ} (hi : i < 2 ^ V.rlen x.length) (hj : j < V.q) :
    proofOf V x w (V.position x (rstr V x.length i) j) = w.getD (i * V.q + j) false := by
  classical
  set p := V.position x (rstr V x.length i) j with hp
  set l := pairsList (2 ^ V.rlen x.length) V.q with hl
  set f : ℕ × ℕ → Bool := fun ij => V.position x (rstr V x.length ij.1) ij.2 == p with hf
  have hmem : (i, j) ∈ l := mem_pairsList.2 ⟨hi, hj⟩
  cases hfind : l.find? f with
  | none =>
      have hne := (List.find?_eq_none.1 hfind) (i, j) hmem
      simp only [hf, beq_iff_eq] at hne
      exact absurd hp.symm hne
  | some ij =>
      have hp' : f ij = true := List.find?_some hfind
      have hmem' : ij ∈ l := List.mem_of_find?_eq_some hfind
      obtain ⟨hi', hj'⟩ := mem_pairsList.1 (show (ij.1, ij.2) ∈ l by simpa using hmem')
      have hposeq : V.position x (rstr V x.length ij.1) ij.2 = p := by
        simpa [hf] using hp'
      have := hcons ij.1 hi' ij.2 hj' i hi j hj (by rw [hposeq, hp])
      simp only [proofOf, ← hl, ← hf, hfind]
      exact this

/-- **The easy inclusion of the PCP theorem**: every language with a `(O(log n), O(1))`
probabilistically checkable proof system is in NP. -/
theorem pcp_subset_np {L : Language} (h : InPCP L) : InNP L := by
  classical
  obtain ⟨V, hcomp, hsound⟩ := h
  obtain ⟨c, k, hpos⟩ := V.pos_size_poly
  refine ⟨{ wlen := fun n => 2 ^ V.rlen n * V.q
            circ := fun n => npCirc V n
            wlen_poly := V.rand_log.mul (isPoly_const V.q)
            size_poly := (isPoly_npSizeBound V c k).mono
              (fun n => size_npCirc_le V hpos n) }, ?_⟩
  intro x
  constructor
  · -- completeness: the honest proof yields a witness
    intro hx
    obtain ⟨pi, hpi⟩ := hcomp x hx
    refine ⟨tableList V.q (2 ^ V.rlen x.length)
      (fun i j => pi (V.position x (rstr V x.length i) j)), by simp, ?_⟩
    set w := tableList V.q (2 ^ V.rlen x.length)
      (fun i j => pi (V.position x (rstr V x.length i) j)) with hw
    have hget : ∀ i < 2 ^ V.rlen x.length, ∀ j < V.q,
        w.getD (i * V.q + j) false = pi (V.position x (rstr V x.length i) j) :=
      fun i hi j hj => tableList_getD hi hj
    show (npCirc V x.length).eval (asFun (x ++ w)) = true
    rw [npCirc_eval_iff]
    constructor
    · intro i hi
      have hr : rstr V x.length i ∈ allBits (V.rlen x.length) :=
        mem_allBits.2 (length_rstr hi)
      have hacc := hpi _ hr
      have hans : ansOf V w i = V.answers x (rstr V x.length i) pi := by
        rw [ansOf, PCPVerifier.answers]
        refine List.map_inj_left.2 ?_
        intro j hj
        exact hget i hi j (by simpa using hj)
      rw [hans]
      exact hacc
    · intro i hi j hj i' hi' j' hj' hposeq
      rw [hget i hi j hj, hget i' hi' j' hj', hposeq]
  · -- soundness: a witness gives a proof accepted with probability 1
    rintro ⟨w, hwlen, hw⟩
    by_contra hx
    have hiff := (npCirc_eval_iff V x w).1 hw
    obtain ⟨hacc, hcons⟩ := hiff
    set pi := proofOf V x w with hpi
    have hall : ∀ r ∈ allBits (V.rlen x.length), V.acc x r pi = true := by
      intro r hr
      obtain ⟨i, hi, rfl⟩ := exists_index_rstr hr
      have hans : V.answers x (rstr V x.length i) pi = ansOf V w i := by
        rw [ansOf, PCPVerifier.answers]
        refine List.map_inj_left.2 ?_
        intro j hj
        exact proofOf_apply V x w hcons hi (by simpa using hj)
      rw [PCPVerifier.acc, hans]
      exact hacc i hi
    have hcount : V.acceptCount x pi = 2 ^ V.rlen x.length := by
      rw [PCPVerifier.acceptCount, List.filter_eq_self.2 hall]
      simp
    have := hsound x hx pi
    rw [hcount] at this
    have hpow : 0 < 2 ^ V.rlen x.length := Nat.two_pow_pos _
    omega

/-! ## Sanity checks: both classes contain the polynomial-size circuit languages -/

/-- Languages decided by a family of polynomial-size circuits (the non-uniform analogue
of `P`). -/
def InPpoly (L : Language) : Prop :=
  ∃ C : ℕ → Circ, IsPoly (fun n => (C n).size) ∧
    ∀ x : List Bool, L x ↔ (C x.length).eval (asFun x) = true

theorem ppoly_subset_np {L : Language} (h : InPpoly L) : InNP L := by
  obtain ⟨C, hpoly, hC⟩ := h
  refine ⟨{ wlen := fun _ => 0, circ := C, wlen_poly := isPoly_const 0,
            size_poly := hpoly }, ?_⟩
  intro x
  rw [hC x]
  constructor
  · intro hx
    exact ⟨[], rfl, by simpa [NPVerifier.Accepts] using hx⟩
  · rintro ⟨w, hw, hacc⟩
    have : w = [] := List.length_eq_zero_iff.1 hw
    subst this
    simpa [NPVerifier.Accepts] using hacc

theorem ppoly_subset_pcp {L : Language} (h : InPpoly L) : InPCP L := by
  obtain ⟨C, hpoly, hC⟩ := h
  refine ⟨{ q := 0, rlen := fun _ => 0, pbits := fun _ => 0,
            posCirc := fun _ _ _ => Circ.cst false, accCirc := C,
            rand_log := by simpa using isPoly_const 1,
            pbits_poly := isPoly_const 0,
            pos_size_poly := ⟨1, 0, by simp [Circ.size]⟩,
            acc_size_poly := hpoly }, ?_, ?_⟩
  · intro x hx
    refine ⟨fun _ => false, ?_⟩
    intro r hr
    have hrnil : r = [] := List.length_eq_zero_iff.1 (mem_allBits.1 hr)
    subst hrnil
    have : (C x.length).eval (asFun x) = true := (hC x).1 hx
    simpa [PCPVerifier.Accepts, PCPVerifier.acc, PCPVerifier.accWith,
      PCPVerifier.answers] using this
  · intro x hx pi
    have hfalse : (C x.length).eval (asFun x) = false := by
      cases hv : (C x.length).eval (asFun x) with
      | false => rfl
      | true => exact absurd ((hC x).2 hv) hx
    simp [PCPVerifier.acceptCount, allBits, PCPVerifier.acc, PCPVerifier.accWith,
      PCPVerifier.answers, hfalse]

/-! ## The PCP theorem -/

/-- **The PCP theorem**, `NP = PCP(log n, O(1))`.

The inclusion `PCP(log n, O(1)) ⊆ NP` is proved here unconditionally
(`CS.pcp_subset_np`).  The converse inclusion `NP ⊆ PCP(log n, O(1))` — the deep half of
the PCP theorem of Arora–Safra and Arora–Lund–Motwani–Sudan–Szegedy — is taken as the
hypothesis `hard`; it is not proved in this development. -/
theorem pcp_theorem (hard : ∀ L : Language, InNP L → InPCP L) :
    {L : Language | InNP L} = {L : Language | InPCP L} :=
  Set.Subset.antisymm (fun _ hL => hard _ hL) (fun _ hL => pcp_subset_np hL)

end CS

/-
Boolean circuits, polynomial bounds, and enumeration of bit strings.

This file provides the elementary infrastructure used to state and study the
PCP theorem in `RequestProject.Main`.
-/
import Mathlib

set_option autoImplicit false

namespace CS

/-! ## Boolean circuits -/

/-- A Boolean circuit (formula) over variables indexed by `ℕ`. -/
inductive Circ where
  | var : ℕ → Circ
  | cst : Bool → Circ
  | neg : Circ → Circ
  | conj : Circ → Circ → Circ
  | disj : Circ → Circ → Circ
  deriving Inhabited

namespace Circ

/-- Evaluation of a circuit under an assignment of the variables. -/
def eval : Circ → (ℕ → Bool) → Bool
  | var i, v => v i
  | cst b, _ => b
  | neg c, v => !(c.eval v)
  | conj a b, v => (a.eval v) && (b.eval v)
  | disj a b, v => (a.eval v) || (b.eval v)

/-- The size (number of gates) of a circuit. -/
def size : Circ → ℕ
  | var _ => 1
  | cst _ => 1
  | neg c => c.size + 1
  | conj a b => a.size + b.size + 1
  | disj a b => a.size + b.size + 1

@[simp] lemma eval_var (i : ℕ) (v : ℕ → Bool) : (var i).eval v = v i := rfl
@[simp] lemma eval_cst (b : Bool) (v : ℕ → Bool) : (cst b).eval v = b := rfl
@[simp] lemma eval_neg (c : Circ) (v : ℕ → Bool) : (neg c).eval v = !(c.eval v) := rfl
@[simp] lemma eval_conj (a b : Circ) (v : ℕ → Bool) :
    (conj a b).eval v = ((a.eval v) && (b.eval v)) := rfl
@[simp] lemma eval_disj (a b : Circ) (v : ℕ → Bool) :
    (disj a b).eval v = ((a.eval v) || (b.eval v)) := rfl

lemma one_le_size (c : Circ) : 1 ≤ c.size := by
  cases c <;> simp [size]

/-- Substitution of circuits for variables. -/
def comp : Circ → (ℕ → Circ) → Circ
  | var i, s => s i
  | cst b, _ => cst b
  | neg c, s => neg (c.comp s)
  | conj a b, s => conj (a.comp s) (b.comp s)
  | disj a b, s => disj (a.comp s) (b.comp s)

lemma eval_comp (c : Circ) (s : ℕ → Circ) (v : ℕ → Bool) :
    (c.comp s).eval v = c.eval (fun i => (s i).eval v) := by
  induction c with
  | var i => rfl
  | cst b => rfl
  | neg c ih => simp [comp, ih]
  | conj a b iha ihb => simp [comp, iha, ihb]
  | disj a b iha ihb => simp [comp, iha, ihb]

lemma size_comp_le (c : Circ) (s : ℕ → Circ) (S : ℕ) (h : ∀ i, (s i).size ≤ S) :
    (c.comp s).size ≤ c.size * (S + 1) := by
  induction c with
  | var i => simpa [comp, size] using le_trans (h i) (Nat.le_succ S)
  | cst b => simp [comp, size]
  | neg c ih =>
      have : (c.comp s).size + 1 ≤ c.size * (S + 1) + (S + 1) := by omega
      simpa [comp, size, Nat.succ_mul, Nat.add_mul] using this
  | conj a b iha ihb =>
      have : (a.comp s).size + (b.comp s).size + 1
          ≤ a.size * (S + 1) + b.size * (S + 1) + (S + 1) := by omega
      simpa [comp, size, Nat.add_mul] using this
  | disj a b iha ihb =>
      have : (a.comp s).size + (b.comp s).size + 1
          ≤ a.size * (S + 1) + b.size * (S + 1) + (S + 1) := by omega
      simpa [comp, size, Nat.add_mul] using this

/-- Conjunction of a list of circuits. -/
def bigAnd : List Circ → Circ
  | [] => cst true
  | c :: cs => conj c (bigAnd cs)

@[simp] lemma eval_bigAnd (l : List Circ) (v : ℕ → Bool) :
    (bigAnd l).eval v = true ↔ ∀ c ∈ l, c.eval v = true := by
  induction l with
  | nil => simp [bigAnd]
  | cons c cs ih => simp [bigAnd, ih]

lemma size_bigAnd_le (l : List Circ) (B : ℕ) (h : ∀ c ∈ l, c.size ≤ B) :
    (bigAnd l).size ≤ l.length * (B + 1) + 1 := by
  induction l with
  | nil => simp [bigAnd, size]
  | cons c cs ih =>
      have hc : c.size ≤ B := h c (by simp)
      have hcs : ∀ d ∈ cs, d.size ≤ B := fun d hd => h d (by simp [hd])
      have := ih hcs
      simp only [bigAnd, size, List.length_cons]
      have : c.size + (bigAnd cs).size + 1 ≤ B + (cs.length * (B + 1) + 1) + 1 := by omega
      calc c.size + (bigAnd cs).size + 1 ≤ B + (cs.length * (B + 1) + 1) + 1 := this
        _ ≤ (cs.length + 1) * (B + 1) + 1 := by ring_nf; omega

/-- The "exclusive nor" gadget: outputs `true` iff the two circuits agree. -/
def xnor (a b : Circ) : Circ := disj (conj a b) (conj (neg a) (neg b))

@[simp] lemma eval_xnor (a b : Circ) (v : ℕ → Bool) :
    (xnor a b).eval v = true ↔ a.eval v = b.eval v := by
  simp only [xnor, eval_disj, eval_conj, eval_neg]
  cases ha : a.eval v <;> cases hb : b.eval v <;> simp

lemma size_xnor (a b : Circ) : (xnor a b).size = 2 * a.size + 2 * b.size + 5 := by
  simp [xnor, size]; ring

/-- Implication gadget. -/
def impl (a b : Circ) : Circ := disj (neg a) b

@[simp] lemma eval_impl (a b : Circ) (v : ℕ → Bool) :
    (impl a b).eval v = true ↔ (a.eval v = true → b.eval v = true) := by
  simp only [impl, eval_disj, eval_neg]
  cases ha : a.eval v <;> cases hb : b.eval v <;> simp

lemma size_impl (a b : Circ) : (impl a b).size = a.size + b.size + 2 := by
  simp [impl, size]; ring

end Circ

/-! ## Polynomial bounds -/

/-- `f` is bounded by a polynomial. -/
def IsPoly (f : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

lemma isPoly_const (a : ℕ) : IsPoly (fun _ => a) := ⟨a, 0, by simp⟩

lemma IsPoly.mono {f g : ℕ → ℕ} (hg : IsPoly g) (h : ∀ n, f n ≤ g n) : IsPoly f := by
  obtain ⟨c, k, hc⟩ := hg
  exact ⟨c, k, fun n => le_trans (h n) (hc n)⟩

lemma IsPoly.add {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun n => f n + g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, max k₁ k₂, fun n => ?_⟩
  have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have e₁ : (n + 1) ^ k₁ ≤ (n + 1) ^ (max k₁ k₂) := Nat.pow_le_pow_right hn (le_max_left _ _)
  have e₂ : (n + 1) ^ k₂ ≤ (n + 1) ^ (max k₁ k₂) := Nat.pow_le_pow_right hn (le_max_right _ _)
  calc f n + g n ≤ c₁ * (n + 1) ^ k₁ + c₂ * (n + 1) ^ k₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ c₁ * (n + 1) ^ (max k₁ k₂) + c₂ * (n + 1) ^ (max k₁ k₂) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e₁) (Nat.mul_le_mul_left _ e₂)
    _ = (c₁ + c₂) * (n + 1) ^ (max k₁ k₂) := by ring

lemma IsPoly.mul {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun n => f n * g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, k₁ + k₂, fun n => ?_⟩
  calc f n * g n ≤ (c₁ * (n + 1) ^ k₁) * (c₂ * (n + 1) ^ k₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = (c₁ * c₂) * (n + 1) ^ (k₁ + k₂) := by ring

lemma isPoly_id : IsPoly (fun n => n) := ⟨1, 1, by intro n; simp⟩

/-! ## Enumeration of bit strings -/

/-- All bit strings of a given length. -/
def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBits n).flatMap (fun l => [false :: l, true :: l])

@[simp] lemma length_allBits (n : ℕ) : (allBits n).length = 2 ^ n := by
  induction n with
  | zero => simp [allBits]
  | succ n ih =>
      simp [allBits, List.length_flatMap, ih, Nat.pow_succ]

@[simp] lemma mem_allBits {l : List Bool} {n : ℕ} : l ∈ allBits n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [allBits, List.length_eq_zero_iff]
  | succ n ih =>
      constructor
      · intro h
        simp only [allBits, List.mem_flatMap] at h
        obtain ⟨t, ht, hmem⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        have hlen : t.length = n := ih.1 ht
        rcases hmem with h | h <;> subst h <;> simp [hlen]
      · intro h
        cases l with
        | nil => simp at h
        | cons b t =>
            simp only [List.length_cons, Nat.succ.injEq] at h
            simp only [allBits, List.mem_flatMap]
            exact ⟨t, ih.2 h, by cases b <;> simp⟩

end CS

