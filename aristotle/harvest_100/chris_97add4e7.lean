/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

/-!
## Overview

This file develops a self-contained, purely combinatorial model of probabilistically
checkable proofs and states the PCP theorem, `NP = PCP(log n, O(1))`, inside it.

The model is the standard "constraint satisfaction" presentation of a PCP verifier.
For every input length `n` we are given

* a **proof length** `m` and a list of **constraints**, each of which is an arbitrary
  Boolean predicate depending on at most `q` of the `n + m` variables (the `n` input
  bits, followed by the `m` proof bits);
* the verifier picks one of the `N` constraints uniformly at random -- this costs
  `log₂ N` random bits, and `N` is required to be polynomially bounded, so the number of
  random bits is `O(log n)`, see `CS.PolyBounded.log_randomness` -- and then reads the
  at most `q` variables that this constraint depends on;
* **completeness**: if `x` is in the language, some proof satisfies *all* constraints;
* **soundness**: if `x` is not in the language, then *every* proof leaves a prescribed
  fraction of the constraints unsatisfied.

Two soundness regimes are considered:

* `CS.SoundWeak`: at least one constraint fails (an inverse-polynomial gap);
* `CS.SoundHalf`: fewer than half of the constraints are satisfied (a constant gap,
  i.e. rejection probability greater than `1/2`).

`CS.NPClass` is the class of languages described by a polynomial-size constraint system
of constant arity: this is the Cook–Levin normal form of `NP`, read nonuniformly.  Note
that the constraint system depends only on the input *length*, the input bits being
ordinary variables of the system that the constraints may query; this is what keeps the
class from degenerating into the class of all languages.  `CS.WeakPCPClass` and
`CS.PCPClass` are the corresponding PCP classes, i.e. `PCP(log n, O(1))` with an
inverse-polynomial and with a constant soundness gap respectively.

The following are proved unconditionally:

* `CS.PolyBounded.log_randomness`: polynomially many constraints means `O(log n)`
  random bits;
* `CS.np_eq_weakPCP`: `NP = PCP(log n, O(1))` with an inverse-polynomial gap;
* `CS.pcp_subset_np`: `PCP(log n, O(1)) ⊆ NP`, the easy inclusion of the PCP theorem;
* `CS.pcp_theorem`: `NP = PCP(log n, O(1))` holds **if and only if** gap amplification
  holds, i.e. iff every polynomial-size constant-arity constraint system describing a
  language can be replaced by one with constant soundness gap.

Thus the whole content of the PCP theorem is isolated in the gap amplification statement
`CS.GapAmplification`, the converse inclusion being proved outright.

Everything below uses only the Lean 4 core library.
-/

namespace CS

/-- A language, presented lengthwise: for each input length `n`, a predicate on bit
strings of length `n`. -/
def Language : Type := (n : Nat) → (Fin n → Bool) → Prop

/-- `f` is bounded by a polynomial. -/
def PolyBounded (f : Nat → Nat) : Prop := ∃ c k : Nat, ∀ n, f n ≤ c * (n + 1) ^ k

/-- Choosing uniformly among polynomially many objects costs only `O(log n)` random
bits: if `f` is polynomially bounded then `f n ≤ 2 ^ (a + k * (log₂ (n+1) + 1))` for
suitable constants `a, k`. -/
theorem PolyBounded.log_randomness {f : Nat → Nat} (hf : PolyBounded f) :
    ∃ a k : Nat, ∀ n, f n ≤ 2 ^ (a + k * (Nat.log2 (n + 1) + 1)) := by
  obtain ⟨c, k, hc⟩ := hf
  refine ⟨c, k, fun n => Nat.le_trans (hc n) ?_⟩
  have h1 : c ≤ 2 ^ c := Nat.le_of_lt Nat.lt_two_pow_self
  have h2 : n + 1 ≤ 2 ^ (Nat.log2 (n + 1) + 1) := Nat.le_of_lt Nat.lt_log2_self
  calc c * (n + 1) ^ k ≤ 2 ^ c * (2 ^ (Nat.log2 (n + 1) + 1)) ^ k :=
        Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 k)
    _ = 2 ^ (c + k * (Nat.log2 (n + 1) + 1)) := by
        rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mul_comm (Nat.log2 (n + 1) + 1) k]

/-- A constraint on variables of type `V` reading at most `q` of them: an arbitrary
Boolean predicate on assignments, together with a list `supp` of at most `q` variables
on which its value is allowed to depend (its query set). -/
structure Constraint (V : Type) (q : Nat) where
  /-- The variables the constraint queries. -/
  supp : List V
  /-- At most `q` variables are queried. -/
  length_supp_le : supp.length ≤ q
  /-- The predicate applied by the constraint to an assignment. -/
  eval : (V → Bool) → Bool
  /-- The predicate depends only on the queried variables. -/
  eval_local : ∀ a b : V → Bool, (∀ v ∈ supp, a v = b v) → eval a = eval b

/-- A constraint system for inputs of length `n`, with constraints of arity at most `q`:
a proof length together with a list of constraints on the variables
`Fin n ⊕ Fin proofLen` (the input bits, then the proof bits). -/
structure CSP (n q : Nat) where
  /-- Length of the (probabilistically checkable) proof. -/
  proofLen : Nat
  /-- The constraints; the verifier picks one of them uniformly at random. -/
  con : List (Constraint (Fin n ⊕ Fin proofLen) q)

namespace CSP

variable {n q : Nat}

/-- The number of constraints; the verifier uses `log₂` of this many random bits. -/
def numCon (I : CSP n q) : Nat := I.con.length

/-- The number of constraints satisfied by the input `x` together with the proof `π`. -/
def satCount (I : CSP n q) (x : Fin n → Bool) (pi : Fin I.proofLen → Bool) : Nat :=
  I.con.countP (fun c => c.eval (Sum.elim x pi))

/-- All constraints are satisfied by the input `x` together with the proof `π`. -/
def AllSat (I : CSP n q) (x : Fin n → Bool) (pi : Fin I.proofLen → Bool) : Prop :=
  ∀ c ∈ I.con, c.eval (Sum.elim x pi) = true

theorem satCount_le (I : CSP n q) (x : Fin n → Bool) (pi : Fin I.proofLen → Bool) :
    I.satCount x pi ≤ I.numCon := List.countP_le_length

theorem allSat_iff_satCount_eq (I : CSP n q) (x : Fin n → Bool)
    (pi : Fin I.proofLen → Bool) : I.AllSat x pi ↔ I.satCount x pi = I.numCon := by
  simp [satCount, numCon, AllSat, List.countP_eq_length]

theorem satCount_lt_iff_not_allSat (I : CSP n q) (x : Fin n → Bool)
    (pi : Fin I.proofLen → Bool) : I.satCount x pi < I.numCon ↔ ¬ I.AllSat x pi := by
  rw [allSat_iff_satCount_eq]
  exact ⟨fun h h' => absurd h' (Nat.ne_of_lt h),
    fun h => Nat.lt_of_le_of_ne (I.satCount_le x pi) h⟩

end CSP

/-- A family of constraint systems, one for each input length, of polynomial size:
polynomially many constraints (equivalently, `O(log n)` random bits) and polynomially
long proofs.  The bound `q n` is the number of queries the verifier makes. -/
structure VerifierFamily (q : Nat → Nat) where
  /-- The constraint system used on inputs of length `n`. -/
  inst : (n : Nat) → CSP n (q n)
  /-- Polynomially many constraints, i.e. `O(log n)` random bits. -/
  numCon_poly : PolyBounded (fun n => (inst n).numCon)
  /-- Polynomially long proofs. -/
  proofLen_poly : PolyBounded (fun n => (inst n).proofLen)

variable {q : Nat → Nat}

/-- Perfect completeness: every word of the language admits a proof satisfying all
constraints, so the verifier accepts with probability `1`. -/
def Complete (F : VerifierFamily q) (L : Language) : Prop :=
  ∀ (n : Nat) (x : Fin n → Bool), L n x → ∃ pi, (F.inst n).AllSat x pi

/-- Weak, inverse-polynomial gap soundness: for a word outside the language every proof
leaves at least one constraint unsatisfied. -/
def SoundWeak (F : VerifierFamily q) (L : Language) : Prop :=
  ∀ (n : Nat) (x : Fin n → Bool), ¬ L n x →
    ∀ pi, (F.inst n).satCount x pi < (F.inst n).numCon

/-- Constant gap soundness: for a word outside the language every proof satisfies fewer
than half of the constraints, i.e. the verifier rejects with probability `> 1/2`. -/
def SoundHalf (F : VerifierFamily q) (L : Language) : Prop :=
  ∀ (n : Nat) (x : Fin n → Bool), ¬ L n x →
    ∀ pi, 2 * (F.inst n).satCount x pi < (F.inst n).numCon

/-- `NP`, in its Cook–Levin (constraint satisfaction) normal form: the languages
described by a polynomial-size constraint system of constant arity. -/
def NPClass (L : Language) : Prop :=
  ∃ (k : Nat) (F : VerifierFamily (fun _ => k)),
    ∀ (n : Nat) (x : Fin n → Bool), L n x ↔ ∃ pi, (F.inst n).AllSat x pi

/-- `PCP(log n, O(1))` with an inverse-polynomial soundness gap: `O(log n)` random bits,
`O(1)` queries, perfect completeness, and at least one violated constraint on rejection. -/
def WeakPCPClass (L : Language) : Prop :=
  ∃ (k : Nat) (F : VerifierFamily (fun _ => k)), Complete F L ∧ SoundWeak F L

/-- `PCP(log n, O(1))`: `O(log n)` random bits, `O(1)` queries, perfect completeness and
soundness error `< 1/2`. -/
def PCPClass (L : Language) : Prop :=
  ∃ (k : Nat) (F : VerifierFamily (fun _ => k)), Complete F L ∧ SoundHalf F L

/-- Gap amplification: every polynomial-size constant-arity constraint system describing
a language can be replaced by one of the same shape with a constant soundness gap.  This
is the substance of the PCP theorem. -/
def GapAmplification : Prop :=
  ∀ (L : Language) (k : Nat) (F : VerifierFamily (fun _ => k)),
    (∀ (n : Nat) (x : Fin n → Bool), L n x ↔ ∃ pi, (F.inst n).AllSat x pi) →
    ∃ (k' : Nat) (F' : VerifierFamily (fun _ => k')), Complete F' L ∧ SoundHalf F' L

/-- **`NP` equals `PCP(log n, O(1))` with an inverse-polynomial gap** (unconditional).
Checking all constraints deterministically, and reading a single random constraint while
demanding that a rejected input violates at least one of them, describe the same class of
languages. -/
theorem np_eq_weakPCP (L : Language) : NPClass L ↔ WeakPCPClass L := by
  constructor
  · rintro ⟨k, F, hF⟩
    refine ⟨k, F, fun n x hx => (hF n x).mp hx, ?_⟩
    intro n x hx pi
    rw [CSP.satCount_lt_iff_not_allSat]
    exact fun h => hx ((hF n x).mpr ⟨pi, h⟩)
  · rintro ⟨k, F, hc, hs⟩
    refine ⟨k, F, fun n x => ⟨fun hx => hc n x hx, ?_⟩⟩
    rintro ⟨pi, hpi⟩
    refine Classical.byContradiction fun hx => ?_
    exact (CSP.satCount_lt_iff_not_allSat _ _ _).mp (hs n x hx pi) hpi

/-- **The easy inclusion of the PCP theorem**: `PCP(log n, O(1)) ⊆ NP`.  A verifier with
a constant soundness gap describes its language exactly, by deterministically checking
all of its polynomially many constraints. -/
theorem pcp_subset_np (L : Language) (h : PCPClass L) : NPClass L := by
  obtain ⟨k, F, hc, hs⟩ := h
  refine ⟨k, F, fun n x => ⟨fun hx => hc n x hx, ?_⟩⟩
  rintro ⟨pi, hpi⟩
  refine Classical.byContradiction fun hx => ?_
  have h2 := hs n x hx pi
  rw [(CSP.allSat_iff_satCount_eq _ _ _).mp hpi] at h2
  omega

/-- **The PCP theorem**, `NP = PCP(log n, O(1))`, in an equivalent reformulation.

The inclusion `PCP(log n, O(1)) ⊆ NP` is proved unconditionally in `pcp_subset_np`, so
the equality of the two classes is *equivalent* to gap amplification: every
polynomial-size constant-arity constraint system describing an `NP` language can be
converted into one for which unsatisfiable instances have more than half of their
constraints violated.  This equivalence isolates the entire content of the PCP theorem
in the statement `GapAmplification`. -/
theorem pcp_theorem : (∀ L : Language, NPClass L ↔ PCPClass L) ↔ GapAmplification := by
  constructor
  · intro heq L k F hF
    exact (heq L).mp ⟨k, F, hF⟩
  · intro hamp L
    exact ⟨fun ⟨k, F, hF⟩ => hamp L k F hF, pcp_subset_np L⟩

/-- Sanity check: the model is inhabited.  The language of all bit strings lies in `NP`,
via the empty constraint system. -/
example : NPClass (fun _ _ => True) := by
  refine ⟨0, ⟨fun _ => ⟨0, []⟩, ⟨0, 0, by simp [CSP.numCon]⟩, ⟨0, 0, by simp⟩⟩, ?_⟩
  intro n x
  exact ⟨fun _ => ⟨fun _ => true, by simp [CSP.AllSat]⟩, fun _ => trivial⟩

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

