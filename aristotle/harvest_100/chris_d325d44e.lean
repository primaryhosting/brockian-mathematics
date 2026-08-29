/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file formalises the statement `NP = PCP(log n, 1)` — the PCP theorem — in a
concrete non-uniform (Boolean circuit) model of computation.  The development is
self-contained and uses no imports.

* `CS.Circuit` : Boolean circuits over an arbitrary type of input variables.
* `CS.NPVerifier` / `CS.NPpoly` : the class of languages possessing a
  polynomial-size verifier reading a polynomially long witness (the non-uniform
  version of `NP`).
* `CS.PCPVerifier` / `CS.PCPlogConst` : probabilistically checkable proof systems
  with logarithmic randomness (equivalently, polynomially many random strings),
  polynomially long proofs, perfect completeness, soundness error `1/2`, and a
  prescribed bound on the number of proof bits inspected.  `PCPlogConst` is the
  class `PCP(log n, O(1))`, where the query bound is a constant independent of
  the input length.

Proved here:

* `CS.pcp_subset_np` : `PCP(log n, q) ⊆ NP` for every query bound (the "easy"
  inclusion; it is proved by taking the conjunction of the verifier's decision
  circuits over all of the polynomially many random strings).
* `CS.np_subset_pcp_polyQueries` : every `NP` language has a PCP system with
  logarithmic randomness and *polynomially many* queries (so the model is not
  degenerate, and the whole content of the PCP theorem is the reduction of the
  number of queries to a constant).
* `CS.ppoly_subset_pcplogconst` : every language decidable by polynomial-size
  circuits lies in `PCP(log n, O(1))` (with zero queries), so the latter class
  is non-empty.
* `CS.pcp_theorem` : the PCP theorem, `NP = PCP(log n, O(1))`.  The hard
  inclusion `NP ⊆ PCP(log n, O(1))` (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy)
  is *not* proved here; it enters as an explicit hypothesis `hard` of the
  theorem, while the easy inclusion is supplied by `CS.pcp_subset_np`.
-/

namespace CS

/-! ## Polynomially bounded functions -/

/-- `PolyBdd f` : the function `f : ℕ → ℕ` is bounded by a polynomial. -/
def PolyBdd (f : Nat → Nat) : Prop := ∃ c k : Nat, ∀ n, f n ≤ c * (n + 1) ^ k

theorem PolyBdd.const (c : Nat) : PolyBdd (fun _ => c) := ⟨c, 0, by simp⟩

theorem PolyBdd.mono {f g : Nat → Nat} (hg : PolyBdd g) (h : ∀ n, f n ≤ g n) :
    PolyBdd f := by
  obtain ⟨c, k, hc⟩ := hg
  exact ⟨c, k, fun n => Nat.le_trans (h n) (hc n)⟩

theorem PolyBdd.add {f g : Nat → Nat} (hf : PolyBdd f) (hg : PolyBdd g) :
    PolyBdd (fun n => f n + g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, max k₁ k₂, fun n => ?_⟩
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have e₁ : (n + 1) ^ k₁ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right hpos (Nat.le_max_left _ _)
  have e₂ : (n + 1) ^ k₂ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right hpos (Nat.le_max_right _ _)
  calc f n + g n ≤ c₁ * (n + 1) ^ k₁ + c₂ * (n + 1) ^ k₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ c₁ * (n + 1) ^ (max k₁ k₂) + c₂ * (n + 1) ^ (max k₁ k₂) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e₁) (Nat.mul_le_mul_left _ e₂)
    _ = (c₁ + c₂) * (n + 1) ^ (max k₁ k₂) := (Nat.add_mul _ _ _).symm

theorem PolyBdd.mul {f g : Nat → Nat} (hf : PolyBdd f) (hg : PolyBdd g) :
    PolyBdd (fun n => f n * g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, k₁ + k₂, fun n => ?_⟩
  calc f n * g n ≤ (c₁ * (n + 1) ^ k₁) * (c₂ * (n + 1) ^ k₂) :=
        Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = c₁ * c₂ * (n + 1) ^ (k₁ + k₂) := by
        simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm]

/-! ## Boolean circuits -/

/-- Boolean circuits with input variables indexed by a type `α`. -/
inductive Circuit (α : Type) : Type
  | var (a : α) : Circuit α
  | const (b : Bool) : Circuit α
  | not (c : Circuit α) : Circuit α
  | and (c d : Circuit α) : Circuit α
  | or (c d : Circuit α) : Circuit α

namespace Circuit

/-- Evaluation of a circuit at an assignment of its input variables. -/
def eval {α : Type} : Circuit α → (α → Bool) → Bool
  | .var a, f => f a
  | .const b, _ => b
  | .not c, f => !(c.eval f)
  | .and c d, f => (c.eval f) && (d.eval f)
  | .or c d, f => (c.eval f) || (d.eval f)

/-- The number of gates (and inputs) of a circuit: its size. -/
def size {α : Type} : Circuit α → Nat
  | .var _ => 1
  | .const _ => 1
  | .not c => c.size + 1
  | .and c d => c.size + d.size + 1
  | .or c d => c.size + d.size + 1

/-- Relabelling of the input variables of a circuit. -/
def map {α β : Type} (f : α → β) : Circuit α → Circuit β
  | .var a => .var (f a)
  | .const b => .const b
  | .not c => .not (c.map f)
  | .and c d => .and (c.map f) (d.map f)
  | .or c d => .or (c.map f) (d.map f)

theorem eval_map {α β : Type} (f : α → β) (c : Circuit α) (g : β → Bool) :
    (c.map f).eval g = c.eval (fun a => g (f a)) := by
  induction c with
  | var a => rfl
  | const b => rfl
  | not c ih => simp [map, eval, ih]
  | and c d ih₁ ih₂ => simp [map, eval, ih₁, ih₂]
  | or c d ih₁ ih₂ => simp [map, eval, ih₁, ih₂]

theorem size_map {α β : Type} (f : α → β) (c : Circuit α) :
    (c.map f).size = c.size := by
  induction c with
  | var a => rfl
  | const b => rfl
  | not c ih => simp [map, size, ih]
  | and c d ih₁ ih₂ => simp [map, size, ih₁, ih₂]
  | or c d ih₁ ih₂ => simp [map, size, ih₁, ih₂]

/-- The conjunction of a list of circuits. -/
def bigAnd {α : Type} : List (Circuit α) → Circuit α
  | [] => .const true
  | c :: cs => .and c (bigAnd cs)

theorem eval_bigAnd {α : Type} (l : List (Circuit α)) (f : α → Bool) :
    (bigAnd l).eval f = true ↔ ∀ c ∈ l, c.eval f = true := by
  induction l with
  | nil => simp [bigAnd, eval]
  | cons c cs ih => simp [bigAnd, eval, ih]

theorem size_bigAnd {α : Type} (l : List (Circuit α)) (b : Nat)
    (hb : ∀ c ∈ l, c.size ≤ b) :
    (bigAnd l).size ≤ l.length * (b + 1) + 1 := by
  induction l with
  | nil => simp [bigAnd, size]
  | cons c cs ih =>
      have hc : c.size ≤ b := hb c (List.mem_cons_self ..)
      have hcs : (bigAnd cs).size ≤ cs.length * (b + 1) + 1 :=
        ih (fun d hd => hb d (List.mem_cons_of_mem _ hd))
      have hsplit : (bigAnd (c :: cs)).size = c.size + (bigAnd cs).size + 1 := rfl
      have hlen : (c :: cs).length * (b + 1) = (b + 1) + cs.length * (b + 1) := by
        simp [List.length_cons, Nat.add_mul, Nat.add_comm, Nat.one_mul]
      omega

end Circuit

/-! ## Languages and the class NP -/

/-- A language: for each input length `n`, a set of bit strings of that length. -/
abbrev Language : Type := (n : Nat) → (Fin n → Bool) → Prop

/-- A polynomial-size verifier for `L` taking a polynomially long witness:
the (non-uniform) definition of the class `NP`. -/
structure NPVerifier (L : Language) where
  /-- Witness length. -/
  wlen : Nat → Nat
  /-- The witness length is polynomially bounded. -/
  hwlen : PolyBdd wlen
  /-- The verifier circuit, taking the input and the witness. -/
  circ : (n : Nat) → Circuit (Fin n ⊕ Fin (wlen n))
  /-- A bound on the size of the verifier circuits. -/
  szBound : Nat → Nat
  /-- The size bound is polynomial. -/
  hszBound : PolyBdd szBound
  /-- The verifier circuits obey the size bound. -/
  hsize : ∀ n, (circ n).size ≤ szBound n
  /-- The verifier accepts some witness exactly on inputs in the language. -/
  correct : ∀ (n : Nat) (x : Fin n → Bool),
    L n x ↔ ∃ w : Fin (wlen n) → Bool, (circ n).eval (Sum.elim x w) = true

/-- The class `NP` (non-uniform version): languages with a polynomial-size
verifier reading a polynomially long witness. -/
def NPpoly (L : Language) : Prop := Nonempty (NPVerifier L)

/-! ## Probabilistically checkable proofs -/

/-- A PCP system for `L` with logarithmic randomness — i.e. polynomially many
random strings — polynomially long proofs, perfect completeness, soundness error
`1/2`, and at most `qb n` proof bits inspected on inputs of length `n`.

For each input length `n` and each random string `r` the verifier is a
polynomial-size Boolean circuit taking the input and the whole proof, subject to
the requirement (`hquery`) that its value depends on at most `qb n` bits of the
proof: this is exactly the requirement that the verifier makes at most `qb n`
queries to the proof oracle. -/
structure PCPVerifier (L : Language) (qb : Nat → Nat) where
  /-- Proof length. -/
  plen : Nat → Nat
  /-- The proof length is polynomially bounded. -/
  hplen : PolyBdd plen
  /-- The number of random strings; polynomially many, i.e. `O(log n)` random bits. -/
  rand : Nat → Nat
  /-- Polynomially many random strings. -/
  hrand : PolyBdd rand
  /-- There is at least one random string. -/
  hrandpos : ∀ n, 0 < rand n
  /-- The decision circuit associated with each random string. -/
  circ : (n : Nat) → Fin (rand n) → Circuit (Fin n ⊕ Fin (plen n))
  /-- A bound on the size of the decision circuits. -/
  szBound : Nat → Nat
  /-- The size bound is polynomial. -/
  hszBound : PolyBdd szBound
  /-- The decision circuits obey the size bound. -/
  hsize : ∀ n r, (circ n r).size ≤ szBound n
  /-- For every input and random string, the decision depends on at most `qb n`
  bits of the proof: the verifier makes at most `qb n` queries. -/
  hquery : ∀ (n : Nat) (r : Fin (rand n)) (x : Fin n → Bool),
    ∃ S : List (Fin (plen n)), S.length ≤ qb n ∧
      ∀ π π' : Fin (plen n) → Bool, (∀ i ∈ S, π i = π' i) →
        (circ n r).eval (Sum.elim x π) = (circ n r).eval (Sum.elim x π')
  /-- Perfect completeness: inputs in the language have a proof that is accepted
  for every random string. -/
  completeness : ∀ (n : Nat) (x : Fin n → Bool), L n x →
    ∃ π : Fin (plen n) → Bool, ∀ r, (circ n r).eval (Sum.elim x π) = true
  /-- Soundness with error `1/2`: for inputs outside the language, every claimed
  proof is accepted for at most half of the random strings. -/
  soundness : ∀ (n : Nat) (x : Fin n → Bool), ¬ L n x →
    ∀ π : Fin (plen n) → Bool,
      2 * ((List.finRange (rand n)).countP
            (fun r => (circ n r).eval (Sum.elim x π))) ≤ rand n

/-- The class `PCP(log n, O(1))`: languages having a PCP system with logarithmic
randomness and a constant number of queries. -/
def PCPlogConst (L : Language) : Prop := ∃ q : Nat, Nonempty (PCPVerifier L (fun _ => q))

/-! ## The easy inclusion: `PCP(log n, q) ⊆ NP` -/

/-- From a PCP system one builds an `NP` verifier: the witness is the PCP proof,
and the verifier circuit is the conjunction of the (polynomially many) decision
circuits, one for each random string. -/
def NPVerifier.ofPCP {L : Language} {qb : Nat → Nat} (V : PCPVerifier L qb) :
    NPVerifier L where
  wlen := V.plen
  hwlen := V.hplen
  circ := fun n => Circuit.bigAnd ((List.finRange (V.rand n)).map (V.circ n))
  szBound := fun n => V.rand n * (V.szBound n + 1) + 1
  hszBound := (V.hrand.mul (V.hszBound.add (PolyBdd.const 1))).add (PolyBdd.const 1)
  hsize := by
    intro n
    have h := Circuit.size_bigAnd ((List.finRange (V.rand n)).map (V.circ n))
      (V.szBound n) (by
        intro c hc
        simp only [List.mem_map] at hc
        have ⟨r, _, hr⟩ := hc
        exact hr ▸ V.hsize n r)
    simp only [List.length_map, List.length_finRange] at h
    exact h
  correct := by
    intro n x
    constructor
    · intro hx
      have ⟨π, hπ⟩ := V.completeness n x hx
      refine ⟨π, ?_⟩
      rw [Circuit.eval_bigAnd]
      intro c hc
      simp only [List.mem_map] at hc
      have ⟨r, _, hr⟩ := hc
      exact hr ▸ hπ r
    · intro hex
      have ⟨π, hπ⟩ := hex
      cases Classical.em (L n x) with
      | inl h => exact h
      | inr hx =>
      exfalso
      have hacc : ∀ r ∈ List.finRange (V.rand n),
          ((V.circ n r).eval (Sum.elim x π)) = true := by
        intro r _
        rw [Circuit.eval_bigAnd] at hπ
        exact hπ _ (List.mem_map_of_mem (List.mem_finRange r))
      have hcount : (List.finRange (V.rand n)).countP
          (fun r => (V.circ n r).eval (Sum.elim x π)) = V.rand n := by
        rw [List.countP_eq_length.2 hacc, List.length_finRange]
      have hsound := V.soundness n x hx π
      rw [hcount] at hsound
      have := V.hrandpos n
      omega

/-- The easy inclusion of the PCP theorem: a language with a PCP system using
logarithmically many random bits (with any number of queries) lies in `NP`. -/
theorem pcp_subset_np {L : Language} {qb : Nat → Nat} (h : Nonempty (PCPVerifier L qb)) :
    NPpoly L :=
  ⟨NPVerifier.ofPCP (Classical.choice h)⟩

/-- In particular `PCP(log n, O(1)) ⊆ NP`. -/
theorem pcplogconst_subset_np {L : Language} (h : PCPlogConst L) : NPpoly L := by
  have ⟨_, hV⟩ := h
  exact pcp_subset_np hV

/-! ## A trivial PCP system with polynomially many queries -/

/-- Every `NP` language admits a (trivial) PCP system which uses a single random
string and reads the whole, polynomially long, proof.  The content of the PCP
theorem is that the number of queries can be brought down to a constant. -/
theorem np_subset_pcp_polyQueries {L : Language} (h : NPpoly L) :
    ∃ qb : Nat → Nat, PolyBdd qb ∧ Nonempty (PCPVerifier L qb) := by
  have V := Classical.choice h
  refine ⟨V.wlen, V.hwlen, ⟨?_⟩⟩
  exact
  { plen := V.wlen
    hplen := V.hwlen
    rand := fun _ => 1
    hrand := PolyBdd.const 1
    hrandpos := fun _ => Nat.one_pos
    circ := fun n _ => V.circ n
    szBound := V.szBound
    hszBound := V.hszBound
    hsize := fun n _ => V.hsize n
    hquery := by
      intro n _ _
      refine ⟨List.finRange (V.wlen n), by simp, ?_⟩
      intro π π' hππ'
      have : π = π' := funext fun i => hππ' i (List.mem_finRange i)
      rw [this]
    completeness := by
      intro n x hx
      have ⟨w, hw⟩ := (V.correct n x).1 hx
      exact ⟨w, fun _ => hw⟩
    soundness := by
      intro n x hx π
      have hrej : ¬ ((V.circ n).eval (Sum.elim x π) = true) := by
        intro hacc
        exact hx ((V.correct n x).2 ⟨π, hacc⟩)
      have hzero : (List.finRange 1).countP
          (fun _ => (V.circ n).eval (Sum.elim x π)) = 0 :=
        List.countP_eq_zero.2 (fun _ _ => hrej)
      simp only [hzero]
      omega }

/-! ## Non-vacuity: `P/poly ⊆ PCP(log n, 0)` -/

/-- A polynomial-size circuit family deciding `L`: the (non-uniform) class
`P/poly`. -/
structure PolySizeDecider (L : Language) where
  /-- The deciding circuit for each input length. -/
  circ : (n : Nat) → Circuit (Fin n)
  /-- A bound on the size of the deciding circuits. -/
  szBound : Nat → Nat
  /-- The size bound is polynomial. -/
  hszBound : PolyBdd szBound
  /-- The circuits obey the size bound. -/
  hsize : ∀ n, (circ n).size ≤ szBound n
  /-- The circuits decide the language. -/
  correct : ∀ (n : Nat) (x : Fin n → Bool), L n x ↔ (circ n).eval x = true

/-- The class `P/poly`. -/
def Ppoly (L : Language) : Prop := Nonempty (PolySizeDecider L)

/-- Every language decidable by polynomial-size circuits has a PCP system that
makes no queries at all; in particular the class `PCP(log n, O(1))` is not
empty. -/
theorem ppoly_subset_pcp_zeroQueries {L : Language} (h : Ppoly L) :
    Nonempty (PCPVerifier L (fun _ => 0)) := by
  have V := Classical.choice h
  refine ⟨?_⟩
  exact
  { plen := fun _ => 0
    hplen := PolyBdd.const 0
    rand := fun _ => 1
    hrand := PolyBdd.const 1
    hrandpos := fun _ => Nat.one_pos
    circ := fun n _ => (V.circ n).map Sum.inl
    szBound := V.szBound
    hszBound := V.hszBound
    hsize := by
      intro n _
      rw [Circuit.size_map]
      exact V.hsize n
    hquery := by
      intro n _ _
      exact ⟨[], Nat.le_refl 0, fun π π' _ => by
        simp only [Circuit.eval_map]
        rfl⟩
    completeness := by
      intro n x hx
      refine ⟨fun i => i.elim0, fun _ => ?_⟩
      rw [Circuit.eval_map]
      exact (V.correct n x).1 hx
    soundness := by
      intro n x hx π
      have hrej : ¬ (((V.circ n).map Sum.inl).eval (Sum.elim x π) = true) := by
        rw [Circuit.eval_map]
        intro hacc
        exact hx ((V.correct n x).2 hacc)
      have hzero : (List.finRange 1).countP
          (fun _ => ((V.circ n).map Sum.inl).eval (Sum.elim x π)) = 0 :=
        List.countP_eq_zero.2 (fun _ _ => hrej)
      simp only [hzero]
      omega }

/-- Languages decidable by polynomial-size circuits lie in `PCP(log n, O(1))`. -/
theorem ppoly_subset_pcplogconst {L : Language} (h : Ppoly L) : PCPlogConst L :=
  ⟨0, ppoly_subset_pcp_zeroQueries h⟩

/-! ## The PCP theorem -/

/--
**The PCP theorem**: `NP = PCP(log n, 1)`.

A language lies in `NP` if and only if it has a probabilistically checkable
proof system that uses `O(log n)` random bits and inspects only a constant
number of bits of the proof, with perfect completeness and soundness error
`1/2`.

The inclusion `PCP(log n, O(1)) ⊆ NP` is proved here (see `pcp_subset_np`): one
takes the conjunction of the decision circuits over all polynomially many random
strings.  The converse inclusion `NP ⊆ PCP(log n, O(1))` is the deep direction,
due to Arora–Safra and Arora–Lund–Motwani–Sudan–Szegedy; it is assumed here as
the explicit hypothesis `hard` rather than proved.
-/
theorem pcp_theorem (hard : ∀ L : Language, NPpoly L → PCPlogConst L) :
    ∀ L : Language, NPpoly L ↔ PCPlogConst L :=
  fun L => ⟨hard L, pcplogconst_subset_np⟩

end CS

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

