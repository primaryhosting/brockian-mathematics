/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean does not allow a module docstring before `import`; the header is repeated verbatim
-- as the module docstring immediately below the imports.)
import Mathlib

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
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

/-!
## Overview

We prove Ladner's theorem: *if `P ≠ NP` then there is an NP-intermediate language*, i.e. a
language in `NP` which is neither in `P` nor `NP`-complete.

Complexity theory is not available in Mathlib, so the development is carried out over an
explicit abstract model of polynomial time computation, packaged as the structure
`PolyFramework` below.  Strings are encoded as natural numbers, the *size* (bit length) of a
string `x` being `Nat.size x`, and a *language* is a function `ℕ → Bool`.

A `PolyFramework` consists of an enumeration `Red : ℕ → ℕ → ℕ` of the polynomial time
computable functions (`Red e` is the function computed by the `e`-th polynomial time program),
together with a degree function `deg` (`Red e` runs in time `(size x + 2) ^ deg e`), subject to
the standard closure properties of polynomial time:  closure under composition, pairing,
conditionals, basic arithmetic, bit counting, *clocked universal simulation* (running a program
with a unary time budget is polynomial), *bounded search* (searching a unary sized range for a
certificate is polynomial) and *iteration* (iterating a polynomial time function a unary number
of times, along an orbit whose sizes stay polynomially bounded, is polynomial).

All of these are standard true facts about polynomial time; they are taken as the hypotheses of
the theorem rather than as Lean `axiom`s, so the final result is axiom clean.
-/

namespace Ladner

/-- The number of set bits of `h` at positions `< m`. -/
def bitsBelow (m h : ℕ) : ℕ := ((List.range m).filter (fun j => h.testBit j)).length

/-- An abstract model of polynomial time computation over `ℕ` (strings encoded as naturals,
size = bit length = `Nat.size`).

`Red e` is the function computed by the `e`-th polynomial-time program, which runs within
`(Nat.size x + 2) ^ deg e` steps on input `x`.  The fields are the standard closure properties
of the class of polynomial time computable functions. -/
structure PolyFramework where
  /-- Enumeration of the polynomial time computable functions. -/
  Red : ℕ → ℕ → ℕ
  /-- The degree of the polynomial time bound of the `e`-th program. -/
  deg : ℕ → ℕ
  /-- The identity is polynomial time. -/
  mem_id : (fun x => x) ∈ Set.range Red
  /-- Constants are polynomial time. -/
  mem_const : ∀ c, (fun _ => c) ∈ Set.range Red
  /-- Polynomial time functions are closed under composition. -/
  mem_comp : ∀ g h, g ∈ Set.range Red → h ∈ Set.range Red →
    (fun x => g (h x)) ∈ Set.range Red
  /-- Polynomial time functions are closed under pairing. -/
  mem_pair : ∀ g h, g ∈ Set.range Red → h ∈ Set.range Red →
    (fun x => Nat.pair (g x) (h x)) ∈ Set.range Red
  /-- First projection of a pair is polynomial time. -/
  mem_fst : (fun x => (Nat.unpair x).1) ∈ Set.range Red
  /-- Second projection of a pair is polynomial time. -/
  mem_snd : (fun x => (Nat.unpair x).2) ∈ Set.range Red
  /-- Bit length is polynomial time. -/
  mem_size : (fun x => Nat.size x) ∈ Set.range Red
  /-- Addition is polynomial time. -/
  mem_add : (fun x => (Nat.unpair x).1 + (Nat.unpair x).2) ∈ Set.range Red
  /-- Multiplication is polynomial time. -/
  mem_mul : (fun x => (Nat.unpair x).1 * (Nat.unpair x).2) ∈ Set.range Red
  /-- Truncated subtraction is polynomial time. -/
  mem_sub : (fun x => (Nat.unpair x).1 - (Nat.unpair x).2) ∈ Set.range Red
  /-- Halving is polynomial time. -/
  mem_div2 : (fun x => x / 2) ∈ Set.range Red
  /-- Comparison is polynomial time. -/
  mem_le : (fun x => if (Nat.unpair x).1 ≤ (Nat.unpair x).2 then 1 else 0) ∈ Set.range Red
  /-- Polynomial time functions are closed under definition by cases. -/
  mem_ite : ∀ p g h, p ∈ Set.range Red → g ∈ Set.range Red → h ∈ Set.range Red →
    (fun x => if p x = 0 then g x else h x) ∈ Set.range Red
  /-- Counting the set bits below a given position is polynomial time. -/
  mem_bits : (fun x => bitsBelow (Nat.unpair x).1 (Nat.unpair x).2) ∈ Set.range Red
  /-- *Clocked universal simulation.*  On input `pair (pair e x) u`, checking whether the time
  bound of program `e` on `x` fits into the unary budget `Nat.size u` and, if so, running it,
  is polynomial time. -/
  mem_sim : (fun x =>
      if (Nat.size (Nat.unpair (Nat.unpair x).1).2 + 2) ^ deg (Nat.unpair (Nat.unpair x).1).1
          ≤ Nat.size (Nat.unpair x).2
      then Red (Nat.unpair (Nat.unpair x).1).1 (Nat.unpair (Nat.unpair x).1).2 + 1
      else 0) ∈ Set.range Red
  /-- *Bounded search.*  On input `pair x u`, searching for `y ≤ Nat.size u` with
  `Red e (pair x y) = 1` is polynomial time. -/
  mem_search : ∀ e, (fun x =>
      if ∃ y ≤ Nat.size (Nat.unpair x).2, Red e (Nat.pair (Nat.unpair x).1 y) = 1
      then 1 else 0) ∈ Set.range Red
  /-- *Iteration.*  If `g` is polynomial time and the sizes along the orbit of `s₀` under `g`
  grow polynomially, then iterating `g` a unary number of times is polynomial time. -/
  mem_iter : ∀ g, g ∈ Set.range Red → ∀ s₀ d, (∀ n, Nat.size (g^[n] s₀) ≤ (n + 2) ^ d) →
    (fun u => g^[Nat.size u] s₀) ∈ Set.range Red

variable (F : PolyFramework)

/-- The class of polynomial time computable functions of the framework `F`. -/
def PF (g : ℕ → ℕ) : Prop := g ∈ Set.range F.Red

/-- A polynomial time computable predicate. -/
def PFb (p : ℕ → Bool) : Prop := PF F (fun x => if p x then 1 else 0)

/-- A language is in `P` when its indicator function is polynomial time computable. -/
def PLang (A : ℕ → Bool) : Prop := PF F (fun x => if A x then 1 else 0)

/-- A language is in `NP` when membership is witnessed by short certificates checkable in
polynomial time. -/
def NPLang (A : ℕ → Bool) : Prop :=
  ∃ (V : ℕ → Bool) (d : ℕ), PLang F V ∧
    (∀ x y, V (Nat.pair x y) = true → y ≤ 2 ^ ((Nat.size x + 2) ^ d)) ∧
    (∀ x, A x = true ↔ ∃ y, V (Nat.pair x y) = true)

/-- Polynomial time many-one reducibility. -/
def PolyReduces (A B : ℕ → Bool) : Prop := ∃ g, PF F g ∧ ∀ x, A x = B (g x)

/-- `NP`-completeness (with respect to polynomial time many-one reductions). -/
def NPComplete (A : ℕ → Bool) : Prop :=
  NPLang F A ∧ ∀ B, NPLang F B → PolyReduces F B A

/-- A sanity check on the definitions: `P ⊆ NP`. -/
theorem NPLang_of_PLang (F : PolyFramework) (A : ℕ → Bool) (h : PLang F A) : NPLang F A := by
  refine ⟨fun z => A (Nat.unpair z).1 && decide ((Nat.unpair z).2 = 0), 0, ?_, ?_, ?_⟩
  · have h1 : PF F (fun z => if A (Nat.unpair z).1 then 1 else 0) := F.mem_comp _ _ h F.mem_fst
    have h2 : PF F (fun z => if decide ((Nat.unpair z).2 = 0) then 1 else 0) := by
      have hle : PF F (fun z => if (Nat.unpair z).2 ≤ 0 then 1 else 0) := by
        have := F.mem_comp _ _ F.mem_le
          (F.mem_pair _ _ F.mem_snd (F.mem_const 0))
        exact Set.mem_of_eq_of_mem (by funext z; simp) this
      exact Set.mem_of_eq_of_mem (by funext z; simp) hle
    have h3 := F.mem_ite _ _ _ (F.mem_comp _ _ (F.mem_sub) (F.mem_pair _ _ (F.mem_const 1) h1))
      h2 (F.mem_const 0)
    refine Set.mem_of_eq_of_mem ?_ h3
    funext z
    by_cases hA : A (Nat.unpair z).1 = true <;> by_cases hz : (Nat.unpair z).2 = 0 <;>
      simp [hA, hz]
  · intro x y hxy
    simp only [Nat.unpair_pair, Bool.and_eq_true, decide_eq_true_eq] at hxy
    simp [hxy.2]
  · intro x
    constructor
    · intro hx
      exact ⟨0, by simp [hx]⟩
    · rintro ⟨y, hy⟩
      simp only [Nat.unpair_pair, Bool.and_eq_true] at hy
      exact hy.1

/-! ### A toolkit of closure lemmas -/

theorem pf_id : PF F (fun x => x) := F.mem_id

theorem pf_const (c : ℕ) : PF F (fun _ => c) := F.mem_const c

theorem pf_comp {g h : ℕ → ℕ} (hg : PF F g) (hh : PF F h) : PF F (fun x => g (h x)) :=
  F.mem_comp g h hg hh

theorem pf_pair {g h : ℕ → ℕ} (hg : PF F g) (hh : PF F h) :
    PF F (fun x => Nat.pair (g x) (h x)) := F.mem_pair g h hg hh

theorem pf_size {g : ℕ → ℕ} (hg : PF F g) : PF F (fun x => Nat.size (g x)) :=
  pf_comp F F.mem_size hg

theorem pf_div2 {g : ℕ → ℕ} (hg : PF F g) : PF F (fun x => g x / 2) :=
  pf_comp F F.mem_div2 hg

theorem pf_add {g h : ℕ → ℕ} (hg : PF F g) (hh : PF F h) : PF F (fun x => g x + h x) := by
  have := pf_comp F F.mem_add (pf_pair F hg hh)
  simpa using this

theorem pf_mul {g h : ℕ → ℕ} (hg : PF F g) (hh : PF F h) : PF F (fun x => g x * h x) := by
  have := pf_comp F F.mem_mul (pf_pair F hg hh)
  simpa using this

theorem pf_sub {g h : ℕ → ℕ} (hg : PF F g) (hh : PF F h) : PF F (fun x => g x - h x) := by
  have := pf_comp F F.mem_sub (pf_pair F hg hh)
  simpa using this

theorem pf_bits {g h : ℕ → ℕ} (hg : PF F g) (hh : PF F h) :
    PF F (fun x => bitsBelow (g x) (h x)) := by
  have := pf_comp F F.mem_bits (pf_pair F hg hh)
  simpa using this

theorem pf_pow {g : ℕ → ℕ} (hg : PF F g) (d : ℕ) : PF F (fun x => (g x) ^ d) := by
  induction d with
  | zero => simpa using pf_const F 1
  | succ n ih =>
      have := pf_mul F ih hg
      simpa [pow_succ] using this

theorem pfb_le {g h : ℕ → ℕ} (hg : PF F g) (hh : PF F h) :
    PFb F (fun x => decide (g x ≤ h x)) := by
  have := pf_comp F F.mem_le (pf_pair F hg hh)
  simpa [PFb] using this

theorem pf_ite {p : ℕ → Bool} {g h : ℕ → ℕ} (hp : PFb F p) (hg : PF F g) (hh : PF F h) :
    PF F (fun x => if p x then g x else h x) := by
  have hp' : PF F (fun x => (1 : ℕ) - (if p x then 1 else 0)) :=
    pf_sub F (pf_const F 1) hp
  have := F.mem_ite _ _ _ hp' hg hh
  refine Set.mem_of_eq_of_mem ?_ this
  funext x
  by_cases hx : p x = true <;> simp [hx]

theorem pfb_ite {p q r : ℕ → Bool} (hp : PFb F p) (hq : PFb F q) (hr : PFb F r) :
    PFb F (fun x => if p x then q x else r x) := by
  have := pf_ite F hp hq hr
  refine Set.mem_of_eq_of_mem ?_ this
  funext x
  by_cases hx : p x = true <;> simp [hx]

theorem pfb_not {p : ℕ → Bool} (hp : PFb F p) : PFb F (fun x => !p x) := by
  have := pf_ite F hp (pf_const F 0) (pf_const F 1)
  refine Set.mem_of_eq_of_mem ?_ this
  funext x
  by_cases hx : p x = true <;> simp [hx]

theorem pfb_and {p q : ℕ → Bool} (hp : PFb F p) (hq : PFb F q) :
    PFb F (fun x => p x && q x) := by
  have := pfb_ite F hp hq (show PFb F (fun _ => false) by simpa [PFb] using pf_const F 0)
  refine Set.mem_of_eq_of_mem ?_ this
  funext x
  by_cases hx : p x = true <;> simp [hx]

theorem pfb_or {p q : ℕ → Bool} (hp : PFb F p) (hq : PFb F q) :
    PFb F (fun x => p x || q x) := by
  have := pfb_ite F hp (show PFb F (fun _ => true) by simpa [PFb] using pf_const F 1) hq
  refine Set.mem_of_eq_of_mem ?_ this
  funext x
  by_cases hx : p x = true <;> simp [hx]

theorem pfb_eq {g h : ℕ → ℕ} (hg : PF F g) (hh : PF F h) :
    PFb F (fun x => decide (g x = h x)) := by
  have := pfb_and F (pfb_le F hg hh) (pfb_le F hh hg)
  refine Set.mem_of_eq_of_mem ?_ this
  funext x
  by_cases hx : g x = h x
  · simp [hx]
  · have hfalse : (decide (g x ≤ h x) && decide (h x ≤ g x)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    simp [hx, hfalse]

theorem pfb_const (b : Bool) : PFb F (fun _ => b) := by
  cases b
  · simpa [PFb] using pf_const F 0
  · simpa [PFb] using pf_const F 1

theorem pf_of_pfb {p : ℕ → Bool} (hp : PFb F p) : PF F (fun x => if p x then 1 else 0) := hp

theorem pfb_xor {p q : ℕ → Bool} (hp : PFb F p) (hq : PFb F q) :
    PFb F (fun x => xor (p x) (q x)) := by
  have := pfb_ite F hp (pfb_not F hq) hq
  refine Set.mem_of_eq_of_mem ?_ this
  funext x
  by_cases hx : p x = true <;> simp [hx]

theorem pf_mod2 {g : ℕ → ℕ} (hg : PF F g) : PF F (fun x => g x % 2) := by
  have := pf_sub F hg (pf_mul F (pf_const F 2) (pf_div2 F hg))
  refine Set.mem_of_eq_of_mem ?_ this
  funext x
  have := Nat.div_add_mod (g x) 2
  omega

/-! ### The clocked simulation and bounded search operations -/

/-- Clocked simulation: with unary budget `Nat.size u`, either the time bound of program `e`
on `x` fits, in which case the value `Red e x + 1` is returned, or `0` ("not ready"). -/
def simval (e x u : ℕ) : ℕ :=
  if (Nat.size x + 2) ^ F.deg e ≤ Nat.size u then F.Red e x + 1 else 0

/-- Bounded search for a certificate `y ≤ Nat.size u` accepted by program `e`. -/
def srch (e x u : ℕ) : ℕ :=
  if ∃ y ≤ Nat.size u, F.Red e (Nat.pair x y) = 1 then 1 else 0

theorem pf_simval {E X U : ℕ → ℕ} (hE : PF F E) (hX : PF F X) (hU : PF F U) :
    PF F (fun x => simval F (E x) (X x) (U x)) := by
  have := pf_comp F F.mem_sim (pf_pair F (pf_pair F hE hX) hU)
  simpa [simval] using this

theorem pf_srch (e : ℕ) {X U : ℕ → ℕ} (hX : PF F X) (hU : PF F U) :
    PF F (fun x => srch F e (X x) (U x)) := by
  have := pf_comp F (F.mem_search e) (pf_pair F hX hU)
  simpa [srch] using this

/-!
## The diagonalizing state machine

The construction is a *lazy diagonalization*.  A machine runs forever; its state at time `n` is
a quadruple `(P, c, s, H)` encoded as a natural number, where

* `P = 2 ^ n` is a unary clock (so `Nat.size P = n + 1` is the budget available at time `n`);
* `c` is the index of the requirement currently being attacked;
* `s` is the current candidate input;
* `H` records, in bit `j`, whether requirement number `j` was completed at time `j`.

Requirement `2 * e` says "program `e` does not decide `A`"; requirement `2 * e + 1` says
"`Red e` is not a polynomial time reduction of `L` to `A`".  At each time step, if the budget
suffices, the current candidate is tested; a successful test advances to the next requirement
and resets the candidate, an unsuccessful test moves to the next candidate.

The function `fF n` is the value of `c` at time `n`, and the diagonal language is
`A x = L x && (fF (Nat.size x)) even`.
-/

/-- The clock component of an encoded state. -/
def prP (z : ℕ) : ℕ := (Nat.unpair (Nat.unpair z).1).1
/-- The requirement component of an encoded state. -/
def prC (z : ℕ) : ℕ := (Nat.unpair (Nat.unpair z).1).2
/-- The candidate component of an encoded state. -/
def prS (z : ℕ) : ℕ := (Nat.unpair (Nat.unpair z).2).1
/-- The history component of an encoded state. -/
def prH (z : ℕ) : ℕ := (Nat.unpair (Nat.unpair z).2).2
/-- Encoding of a state. -/
def mkst (P c s H : ℕ) : ℕ := Nat.pair (Nat.pair P c) (Nat.pair s H)

@[simp] theorem prP_mkst (P c s H : ℕ) : prP (mkst P c s H) = P := by simp [prP, mkst]
@[simp] theorem prC_mkst (P c s H : ℕ) : prC (mkst P c s H) = c := by simp [prC, mkst]
@[simp] theorem prS_mkst (P c s H : ℕ) : prS (mkst P c s H) = s := by simp [prS, mkst]
@[simp] theorem prH_mkst (P c s H : ℕ) : prH (mkst P c s H) = H := by simp [prH, mkst]

/-- The value returned by the clocked simulation of the program under attack on the current
candidate. -/
def mval (F : PolyFramework) (z : ℕ) : ℕ := simval F (prC z / 2) (prS z) (prP z)

/-- The output of the program under attack on the current candidate (meaningful once the
simulation is ready). -/
def yval (F : PolyFramework) (z : ℕ) : ℕ := mval F z - 1

/-- Is the budget large enough to decide `L` on `x` by brute force over certificates? -/
def bready (dL x u : ℕ) : Bool := decide ((Nat.size x + 2) ^ dL + 1 ≤ Nat.size (Nat.size u))

/-- Readiness of the test at an even numbered requirement. -/
def readyE (F : PolyFramework) (dL z : ℕ) : Bool :=
  decide (mval F z ≠ 0) && bready dL (prS z) (prP z) &&
    decide (Nat.size (prS z) + 1 ≤ Nat.size (prP z))

/-- Readiness of the test at an odd numbered requirement. -/
def readyO (F : PolyFramework) (dL z : ℕ) : Bool :=
  readyE F dL z && bready dL (yval F z) (prP z) &&
    decide (Nat.size (yval F z) + 1 ≤ Nat.size (prP z))

/-- Is the current test affordable? -/
def stReady (F : PolyFramework) (dL z : ℕ) : Bool :=
  if prC z % 2 = 0 then readyE F dL z else readyO F dL z

/-- Does the current test succeed, i.e. is the current candidate a witness against the current
requirement? -/
noncomputable def stWitness (F : PolyFramework) (vIdx z : ℕ) : Bool :=
  if prC z % 2 = 0 then
    xor (decide (yval F z = 1))
      (decide (srch F vIdx (prS z) (prP z) = 1) &&
        decide (bitsBelow (Nat.size (prS z)) (prH z) % 2 = 0))
  else
    xor (decide (srch F vIdx (prS z) (prP z) = 1))
      (decide (srch F vIdx (yval F z) (prP z) = 1) &&
        decide (bitsBelow (Nat.size (yval F z)) (prH z) % 2 = 0))

/-- One step of the diagonalizing machine. -/
noncomputable def step (F : PolyFramework) (vIdx dL z : ℕ) : ℕ :=
  if stReady F dL z then
    (if stWitness F vIdx z then mkst (2 * prP z) (prC z + 1) 0 (prH z + prP z)
      else mkst (2 * prP z) (prC z) (prS z + 1) (prH z))
  else mkst (2 * prP z) (prC z) (prS z) (prH z)

/-- The initial state. -/
def s0 : ℕ := mkst 1 0 0 0

/-- The state of the diagonalizing machine at time `n`. -/
noncomputable def stateAt (F : PolyFramework) (vIdx dL n : ℕ) : ℕ :=
  (step F vIdx dL)^[n] s0

/-- The requirement index reached at time `n`: the "gap function" of Ladner's construction. -/
noncomputable def fF (F : PolyFramework) (vIdx dL n : ℕ) : ℕ := prC (stateAt F vIdx dL n)

/-- The diagonal language. -/
noncomputable def Adiag (F : PolyFramework) (vIdx dL : ℕ) (L : ℕ → Bool) (x : ℕ) : Bool :=
  L x && decide (fF F vIdx dL (Nat.size x) % 2 = 0)

/-! ### The step function is polynomial time -/

theorem pf_congr {F : PolyFramework} {g h : ℕ → ℕ} (hg : PF F g) (e : g = h) : PF F h := e ▸ hg

theorem pfb_congr {F : PolyFramework} {p q : ℕ → Bool} (hp : PFb F p) (e : p = q) : PFb F q :=
  e ▸ hp

variable (F : PolyFramework) (vIdx dL : ℕ)

theorem pf_prP : PF F prP := pf_congr (pf_comp F F.mem_fst F.mem_fst) rfl
theorem pf_prC : PF F prC := pf_congr (pf_comp F F.mem_snd F.mem_fst) rfl
theorem pf_prS : PF F prS := pf_congr (pf_comp F F.mem_fst F.mem_snd) rfl
theorem pf_prH : PF F prH := pf_congr (pf_comp F F.mem_snd F.mem_snd) rfl

theorem pf_mval : PF F (mval F) :=
  pf_simval F (pf_div2 F (pf_prC F)) (pf_prS F) (pf_prP F)

theorem pf_yval : PF F (yval F) := pf_sub F (pf_mval F) (pf_const F 1)

theorem pfb_bready {X U : ℕ → ℕ} (hX : PF F X) (hU : PF F U) :
    PFb F (fun z => bready dL (X z) (U z)) := by
  have := pfb_le F (pf_add F (pf_pow F (pf_add F (pf_size F hX) (pf_const F 2)) dL)
      (pf_const F 1)) (pf_size F (pf_size F hU))
  simpa [bready] using this

theorem pfb_readyE : PFb F (readyE F dL) := by
  have h1 : PFb F (fun z => decide (mval F z ≠ 0)) := by
    refine pfb_congr (pfb_not F (pfb_eq F (pf_mval F) (pf_const F 0))) ?_
    funext z; simp
  have h2 : PFb F (fun z => bready dL (prS z) (prP z)) :=
    pfb_bready F dL (pf_prS F) (pf_prP F)
  have h3 : PFb F (fun z => decide (Nat.size (prS z) + 1 ≤ Nat.size (prP z))) :=
    pfb_le F (pf_add F (pf_size F (pf_prS F)) (pf_const F 1)) (pf_size F (pf_prP F))
  have := pfb_and F (pfb_and F h1 h2) h3
  refine pfb_congr this ?_
  funext z
  simp [readyE]

theorem pfb_readyO : PFb F (readyO F dL) := by
  have h2 : PFb F (fun z => bready dL (yval F z) (prP z)) :=
    pfb_bready F dL (pf_yval F) (pf_prP F)
  have h3 : PFb F (fun z => decide (Nat.size (yval F z) + 1 ≤ Nat.size (prP z))) :=
    pfb_le F (pf_add F (pf_size F (pf_yval F)) (pf_const F 1)) (pf_size F (pf_prP F))
  have := pfb_and F (pfb_and F (pfb_readyE F dL) h2) h3
  refine pfb_congr this ?_
  funext z
  simp [readyO]

theorem pfb_parity : PFb F (fun z => decide (prC z % 2 = 0)) :=
  pfb_eq F (pf_mod2 F (pf_prC F)) (pf_const F 0)

theorem pfb_stReady : PFb F (stReady F dL) := by
  have := pfb_ite F (pfb_parity F) (pfb_readyE F dL) (pfb_readyO F dL)
  refine pfb_congr this ?_
  funext z
  by_cases hz : prC z % 2 = 0 <;> simp [stReady, hz]

theorem pfb_stWitness : PFb F (stWitness F vIdx) := by
  have hA : PFb F (fun z => decide (yval F z = 1)) := pfb_eq F (pf_yval F) (pf_const F 1)
  have hB : PFb F (fun z => decide (srch F vIdx (prS z) (prP z) = 1)) :=
    pfb_eq F (pf_srch F vIdx (pf_prS F) (pf_prP F)) (pf_const F 1)
  have hC : PFb F (fun z => decide (bitsBelow (Nat.size (prS z)) (prH z) % 2 = 0)) :=
    pfb_eq F (pf_mod2 F (pf_bits F (pf_size F (pf_prS F)) (pf_prH F))) (pf_const F 0)
  have hD : PFb F (fun z => decide (srch F vIdx (yval F z) (prP z) = 1)) :=
    pfb_eq F (pf_srch F vIdx (pf_yval F) (pf_prP F)) (pf_const F 1)
  have hE : PFb F (fun z => decide (bitsBelow (Nat.size (yval F z)) (prH z) % 2 = 0)) :=
    pfb_eq F (pf_mod2 F (pf_bits F (pf_size F (pf_yval F)) (pf_prH F))) (pf_const F 0)
  have := pfb_ite F (pfb_parity F) (pfb_xor F hA (pfb_and F hB hC))
    (pfb_xor F hB (pfb_and F hD hE))
  refine pfb_congr this ?_
  funext z
  by_cases hz : prC z % 2 = 0 <;> simp [stWitness, hz]

theorem pf_step : PF F (step F vIdx dL) := by
  have hP2 : PF F (fun z => 2 * prP z) := pf_mul F (pf_const F 2) (pf_prP F)
  have h1 : PF F (fun z => mkst (2 * prP z) (prC z + 1) 0 (prH z + prP z)) :=
    pf_pair F (pf_pair F hP2 (pf_add F (pf_prC F) (pf_const F 1)))
      (pf_pair F (pf_const F 0) (pf_add F (pf_prH F) (pf_prP F)))
  have h2 : PF F (fun z => mkst (2 * prP z) (prC z) (prS z + 1) (prH z)) :=
    pf_pair F (pf_pair F hP2 (pf_prC F))
      (pf_pair F (pf_add F (pf_prS F) (pf_const F 1)) (pf_prH F))
  have h3 : PF F (fun z => mkst (2 * prP z) (prC z) (prS z) (prH z)) :=
    pf_pair F (pf_pair F hP2 (pf_prC F)) (pf_pair F (pf_prS F) (pf_prH F))
  exact pf_ite F (pfb_stReady F dL) (pf_ite F (pfb_stWitness F vIdx) h1 h2) h3

/-! ### The orbit of the initial state -/

/-- Whether the machine completes a requirement at time `n`. -/
noncomputable def jmp (n : ℕ) : Bool :=
  stReady F dL (stateAt F vIdx dL n) && stWitness F vIdx (stateAt F vIdx dL n)

theorem stateAt_succ (n : ℕ) :
    stateAt F vIdx dL (n + 1) = step F vIdx dL (stateAt F vIdx dL n) := by
  simp [stateAt, Function.iterate_succ_apply']

theorem step_prP (z : ℕ) : prP (step F vIdx dL z) = 2 * prP z := by
  unfold step
  split
  · split <;> simp
  · simp

theorem step_prC (z : ℕ) :
    prC (step F vIdx dL z) =
      if stReady F dL z && stWitness F vIdx z then prC z + 1 else prC z := by
  unfold step
  by_cases h1 : stReady F dL z = true <;> by_cases h2 : stWitness F vIdx z = true <;>
    simp [h1, h2]

theorem step_prS (z : ℕ) :
    prS (step F vIdx dL z) =
      if stReady F dL z then (if stWitness F vIdx z then 0 else prS z + 1) else prS z := by
  unfold step
  by_cases h1 : stReady F dL z = true <;> by_cases h2 : stWitness F vIdx z = true <;>
    simp [h1, h2]

theorem step_prH (z : ℕ) :
    prH (step F vIdx dL z) =
      if stReady F dL z && stWitness F vIdx z then prH z + prP z else prH z := by
  unfold step
  by_cases h1 : stReady F dL z = true <;> by_cases h2 : stWitness F vIdx z = true <;>
    simp [h1, h2]

theorem inv_P (n : ℕ) : prP (stateAt F vIdx dL n) = 2 ^ n := by
  induction n with
  | zero => simp [stateAt, s0]
  | succ n ih => rw [stateAt_succ, step_prP, ih]; ring

theorem inv_C_le (n : ℕ) : prC (stateAt F vIdx dL n) ≤ n := by
  induction n with
  | zero => simp [stateAt, s0]
  | succ n ih =>
      rw [stateAt_succ, step_prC]
      split <;> omega

theorem inv_S_le (n : ℕ) : prS (stateAt F vIdx dL n) ≤ n := by
  induction n with
  | zero => simp [stateAt, s0]
  | succ n ih =>
      rw [stateAt_succ, step_prS]
      split
      · split <;> omega
      · omega

theorem inv_H_lt (n : ℕ) : prH (stateAt F vIdx dL n) < 2 ^ n := by
  induction n with
  | zero => simp [stateAt, s0]
  | succ n ih =>
      rw [stateAt_succ, step_prH, inv_P]
      have : (2:ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      split <;> omega

theorem pair_lt_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    Nat.pair a b < 2 ^ (2 * k) := by
  have h : Nat.pair a b < (max a b + 1) * (max a b + 1) := by
    unfold Nat.pair
    rcases lt_or_ge a b with h | h
    · have hmax : max a b = b := by omega
      rw [if_pos h, hmax]
      nlinarith [Nat.le_of_lt h]
    · have hmax : max a b = a := by omega
      rw [if_neg (Nat.not_lt.mpr h), hmax]
      nlinarith
  have hm : max a b + 1 ≤ 2 ^ k := by
    rcases le_total a b with hab | hab
    · simp [max_eq_right hab]; omega
    · simp [max_eq_left hab]; omega
  calc Nat.pair a b < (max a b + 1) * (max a b + 1) := h
    _ ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul hm hm
    _ = 2 ^ (2 * k) := by rw [← pow_add]; ring_nf

theorem size_stateAt (n : ℕ) : Nat.size (stateAt F vIdx dL n) ≤ (n + 2) ^ 3 := by
  have hP : prP (stateAt F vIdx dL n) < 2 ^ (n + 1) := by
    rw [inv_P]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hC : prC (stateAt F vIdx dL n) < 2 ^ (n + 1) :=
    lt_of_le_of_lt (inv_C_le F vIdx dL n) (Nat.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hS : prS (stateAt F vIdx dL n) < 2 ^ (n + 1) :=
    lt_of_le_of_lt (inv_S_le F vIdx dL n) (Nat.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hH : prH (stateAt F vIdx dL n) < 2 ^ (n + 1) :=
    (inv_H_lt F vIdx dL n).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hz : stateAt F vIdx dL n < 2 ^ (4 * (n + 1)) := by
    have h1 := pair_lt_pow hP hC
    have h2 := pair_lt_pow hS hH
    have := pair_lt_pow h1 h2
    have he : stateAt F vIdx dL n =
        Nat.pair (Nat.pair (prP (stateAt F vIdx dL n)) (prC (stateAt F vIdx dL n)))
          (Nat.pair (prS (stateAt F vIdx dL n)) (prH (stateAt F vIdx dL n))) := by
      simp [prP, prC, prS, prH]
    rw [he]
    have h4 : 2 * (2 * (n + 1)) = 4 * (n + 1) := by ring
    rwa [h4] at this
  have := Nat.size_le.mpr hz
  refine this.trans ?_
  nlinarith [sq_nonneg n]

theorem pf_stateAt : PF F (fun u => stateAt F vIdx dL (Nat.size u)) :=
  F.mem_iter (step F vIdx dL) (pf_step F vIdx dL) s0 3 (size_stateAt F vIdx dL)

/-- The "holes" language `{x | fF (size x) is even}` is polynomial time. -/
theorem pfb_even_fF : PFb F (fun x => decide (fF F vIdx dL (Nat.size x) % 2 = 0)) := by
  have h : PF F (fun x => fF F vIdx dL (Nat.size x)) :=
    pf_congr (pf_comp F (pf_prC F) (pf_stateAt F vIdx dL)) rfl
  exact pfb_eq F (pf_mod2 F h) (pf_const F 0)

/-! ### The history register records the jumps -/

theorem fF_zero : fF F vIdx dL 0 = 0 := by simp [fF, stateAt, s0]

theorem fF_succ (n : ℕ) :
    fF F vIdx dL (n + 1) = fF F vIdx dL n + (if jmp F vIdx dL n then 1 else 0) := by
  rw [fF, stateAt_succ, step_prC]
  by_cases hb : jmp F vIdx dL n = true
  · rw [jmp] at hb; simp [fF, hb, jmp]
  · rw [jmp] at hb; simp [fF, hb, jmp]

theorem fF_le_succ (n : ℕ) : fF F vIdx dL n ≤ fF F vIdx dL (n + 1) := by
  rw [fF_succ]; split <;> omega

theorem fF_mono : Monotone (fF F vIdx dL) :=
  monotone_nat_of_le_succ (fF_le_succ F vIdx dL)

theorem fF_eq_count (m : ℕ) :
    fF F vIdx dL m = ((List.range m).filter (jmp F vIdx dL)).length := by
  induction m with
  | zero => simp [fF_zero]
  | succ m ih =>
      rw [fF_succ, ih, List.range_succ, List.filter_append]
      by_cases hb : jmp F vIdx dL m = true <;> simp [hb]

theorem testBit_prH (n j : ℕ) (hj : j < n) :
    (prH (stateAt F vIdx dL n)).testBit j = jmp F vIdx dL j := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [stateAt_succ, step_prH, inv_P]
      have hjmp : (stReady F dL (stateAt F vIdx dL n) &&
          stWitness F vIdx (stateAt F vIdx dL n)) = jmp F vIdx dL n := rfl
      rw [hjmp]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · by_cases hb : jmp F vIdx dL n = true
        · rw [if_pos hb, Nat.add_comm, Nat.testBit_two_pow_add_gt h]
          exact ih h
        · rw [if_neg (by simpa using hb)]
          exact ih h
      · subst h
        by_cases hb : jmp F vIdx dL j = true
        · rw [if_pos hb, Nat.add_comm, Nat.testBit_two_pow_add_eq,
            Nat.testBit_eq_false_of_lt (inv_H_lt F vIdx dL j)]
          simp [hb]
        · rw [if_neg (by simpa using hb),
            Nat.testBit_eq_false_of_lt (inv_H_lt F vIdx dL j)]
          simpa using hb

theorem bitsBelow_prH (n m : ℕ) (h : m ≤ n) :
    bitsBelow m (prH (stateAt F vIdx dL n)) = fF F vIdx dL m := by
  rw [bitsBelow, fF_eq_count]
  congr 1
  refine List.filter_congr ?_
  intro j hj
  simp only [List.mem_range] at hj
  exact testBit_prH F vIdx dL n j (by omega)

/-! ### Basic facts about the classes `P` and `NP` -/

theorem pfb_comp {p : ℕ → Bool} {g : ℕ → ℕ} (hp : PFb F p) (hg : PF F g) :
    PFb F (fun x => p (g x)) := by
  have := pf_comp F hp hg
  exact pf_congr this rfl

theorem pf_Red (e : ℕ) : PF F (F.Red e) := ⟨e, rfl⟩

/-- The languages in `P` are exactly those decided by some program of the enumeration. -/
theorem PLang_iff_Mach (A : ℕ → Bool) :
    PLang F A ↔ ∃ e, ∀ x, A x = decide (F.Red e x = 1) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, fun x => ?_⟩
    have : F.Red e x = if A x then 1 else 0 := congrFun he x
    rw [this]
    by_cases hx : A x = true <;> simp [hx]
  · rintro ⟨e, he⟩
    have : PF F (fun x => if decide (F.Red e x = 1) then 1 else 0) :=
      pf_ite F (pfb_eq F (pf_Red F e) (pf_const F 1)) (pf_const F 1) (pf_const F 0)
    refine pf_congr this ?_
    funext x
    rw [he x]

/-- `P` is closed under finite modifications. -/
theorem PLang_of_eventually_eq :
    ∀ (N : ℕ) (A B : ℕ → Bool), PLang F A → (∀ x, N ≤ x → B x = A x) → PLang F B := by
  intro N
  induction N with
  | zero =>
      intro A B hA hB
      have : B = A := funext fun x => hB x (Nat.zero_le x)
      rw [this]; exact hA
  | succ N ih =>
      intro A B hA hB
      refine ih (fun x => if x = N then B N else A x) B ?_ ?_
      · have : PF F (fun x =>
            if decide (x = N) then (if B N then 1 else 0) else (if A x then 1 else 0)) :=
          pf_ite F (pfb_eq F (pf_id F) (pf_const F N))
            (pf_const F (if B N then 1 else 0)) hA
        refine pf_congr this ?_
        funext x
        by_cases hx : x = N <;> simp [hx]
      · intro x hx
        rcases eq_or_lt_of_le hx with h | h
        · simp [← h]
        · have hxN : x ≠ N := by omega
          simp [hxN]
          exact hB x (by omega)

/-! ### Semantics of the tests performed by the machine -/

/-- Once the budget suffices, the bounded search decides `L`. -/
theorem srch_eq_L (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (x u : ℕ) (h : bready dL x u = true) :
    (srch F vIdx x u = 1) ↔ L x = true := by
  have hb : (Nat.size x + 2) ^ dL + 1 ≤ Nat.size (Nat.size u) := by
    simpa [bready] using h
  have hlt : (Nat.size x + 2) ^ dL < Nat.size (Nat.size u) := by omega
  have hpow : 2 ^ ((Nat.size x + 2) ^ dL) ≤ Nat.size u := Nat.lt_size.mp hlt
  constructor
  · intro hs
    have : ∃ y ≤ Nat.size u, F.Red vIdx (Nat.pair x y) = 1 := by
      by_contra hcon
      rw [srch, if_neg hcon] at hs
      exact absurd hs (by norm_num)
    obtain ⟨y, _, hy⟩ := this
    exact (hLdef x).mpr ⟨y, hy⟩
  · intro hx
    obtain ⟨y, hy⟩ := (hLdef x).mp hx
    have hyle : y ≤ Nat.size u := le_trans (hcert x y hy) hpow
    rw [srch, if_pos ⟨y, hyle, hy⟩]

theorem readyE_mval {z : ℕ} (h : readyE F dL z = true) : mval F z ≠ 0 := by
  simp [readyE] at h; tauto

theorem readyE_bready {z : ℕ} (h : readyE F dL z = true) :
    bready dL (prS z) (prP z) = true := by
  simp [readyE] at h; tauto

theorem readyE_size {z : ℕ} (h : readyE F dL z = true) :
    Nat.size (prS z) + 1 ≤ Nat.size (prP z) := by
  simp [readyE] at h; tauto

theorem readyO_readyE {z : ℕ} (h : readyO F dL z = true) : readyE F dL z = true := by
  simp [readyO] at h; tauto

theorem readyO_bready {z : ℕ} (h : readyO F dL z = true) :
    bready dL (yval F z) (prP z) = true := by
  simp [readyO] at h; tauto

theorem readyO_size {z : ℕ} (h : readyO F dL z = true) :
    Nat.size (yval F z) + 1 ≤ Nat.size (prP z) := by
  simp [readyO] at h; tauto

theorem yval_of_readyE {z : ℕ} (h : readyE F dL z = true) :
    yval F z = F.Red (prC z / 2) (prS z) := by
  have h1 : mval F z ≠ 0 := readyE_mval F dL h
  by_cases hc : (Nat.size (prS z) + 2) ^ F.deg (prC z / 2) ≤ Nat.size (prP z)
  · rw [yval, mval, simval, if_pos hc]; omega
  · exact absurd (by rw [mval, simval, if_neg hc]) h1

theorem size_prP_stateAt (n : ℕ) : Nat.size (prP (stateAt F vIdx dL n)) = n + 1 := by
  rw [inv_P, Nat.size_pow]

/-- The value the machine computes for the diagonal language on `x` at time `n` is the true
value, as soon as the budget suffices. -/
theorem Aval_eq (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (n x : ℕ) (hb : bready dL x (prP (stateAt F vIdx dL n)) = true)
    (hs : Nat.size x + 1 ≤ Nat.size (prP (stateAt F vIdx dL n))) :
    (decide (srch F vIdx x (prP (stateAt F vIdx dL n)) = 1) &&
        decide (bitsBelow (Nat.size x) (prH (stateAt F vIdx dL n)) % 2 = 0)) =
      Adiag F vIdx dL L x := by
  have hsn : Nat.size x ≤ n := by
    rw [size_prP_stateAt] at hs; omega
  have hbits : bitsBelow (Nat.size x) (prH (stateAt F vIdx dL n)) =
      fF F vIdx dL (Nat.size x) := bitsBelow_prH F vIdx dL n _ hsn
  have hL := srch_eq_L F vIdx dL L hcert hLdef x (prP (stateAt F vIdx dL n)) hb
  rw [hbits, Adiag]
  by_cases h1 : L x = true
  · simp [h1, hL.mpr h1]
  · have : ¬ (srch F vIdx x (prP (stateAt F vIdx dL n)) = 1) := fun hcon => h1 (hL.mp hcon)
    simp [h1, this]

theorem stWitness_even (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (n : ℕ) (hpar : prC (stateAt F vIdx dL n) % 2 = 0)
    (hr : readyE F dL (stateAt F vIdx dL n) = true) :
    stWitness F vIdx (stateAt F vIdx dL n) =
      xor (decide (F.Red (prC (stateAt F vIdx dL n) / 2) (prS (stateAt F vIdx dL n)) = 1))
        (Adiag F vIdx dL L (prS (stateAt F vIdx dL n))) := by
  rw [stWitness, if_pos hpar, yval_of_readyE F dL hr,
    Aval_eq F vIdx dL L hcert hLdef n _ (readyE_bready F dL hr) (readyE_size F dL hr)]

theorem stWitness_odd (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (n : ℕ) (hpar : prC (stateAt F vIdx dL n) % 2 ≠ 0)
    (hr : readyO F dL (stateAt F vIdx dL n) = true) :
    stWitness F vIdx (stateAt F vIdx dL n) =
      xor (L (prS (stateAt F vIdx dL n)))
        (Adiag F vIdx dL L
          (F.Red (prC (stateAt F vIdx dL n) / 2) (prS (stateAt F vIdx dL n)))) := by
  have hrE := readyO_readyE F dL hr
  have hy := yval_of_readyE F dL hrE
  have h1 : decide (srch F vIdx (prS (stateAt F vIdx dL n))
      (prP (stateAt F vIdx dL n)) = 1) = L (prS (stateAt F vIdx dL n)) := by
    have := srch_eq_L F vIdx dL L hcert hLdef (prS (stateAt F vIdx dL n))
      (prP (stateAt F vIdx dL n)) (readyE_bready F dL hrE)
    by_cases h : L (prS (stateAt F vIdx dL n)) = true
    · simp [h, this.mpr h]
    · have : ¬ (srch F vIdx (prS (stateAt F vIdx dL n)) (prP (stateAt F vIdx dL n)) = 1) :=
        fun hcon => h (this.mp hcon)
      simp [h, this]
  have h2 := Aval_eq F vIdx dL L hcert hLdef n (yval F (stateAt F vIdx dL n))
    (readyO_bready F dL hr) (readyO_size F dL hr)
  rw [stWitness, if_neg hpar, h1, h2, hy]

/-! ### Every test eventually becomes affordable -/

theorem eventually_readyO (c s : ℕ) : ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ z, prC z = c → prS z = s → prP z = 2 ^ n → readyO F dL z = true := by
  set e := c / 2 with he
  set y := F.Red e s with hy
  set K := max (max ((Nat.size s + 2) ^ F.deg e) ((Nat.size s + 2) ^ dL + 1))
    (max (Nat.size s + 1) (max ((Nat.size y + 2) ^ dL + 1) (Nat.size y + 1))) with hK
  refine ⟨2 ^ K, fun n hn z hc hs hp => ?_⟩
  have hsize : Nat.size (prP z) = n + 1 := by rw [hp, Nat.size_pow]
  have hKn : K ≤ n + 1 := le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (by omega)
  have hK2 : K < Nat.size (Nat.size (prP z)) := by
    rw [hsize]
    refine Nat.lt_size.mpr ?_
    omega
  have hmv : mval F z = y + 1 := by
    rw [mval, simval, hc, hs, ← he, hsize, if_pos (by omega), hy]
  have h1 : mval F z ≠ 0 := by omega
  have h2 : bready dL (prS z) (prP z) = true := by
    rw [bready, hs]
    simp only [decide_eq_true_eq]
    omega
  have h3 : Nat.size (prS z) + 1 ≤ Nat.size (prP z) := by
    rw [hs, hsize]; omega
  have hyv : yval F z = y := by rw [yval, hmv]; omega
  have h4 : bready dL (yval F z) (prP z) = true := by
    rw [bready, hyv]
    simp only [decide_eq_true_eq]
    omega
  have h5 : Nat.size (yval F z) + 1 ≤ Nat.size (prP z) := by
    rw [hyv, hsize]; omega
  simp [readyO, readyE, h1, h2, h3, h4, h5]

theorem stReady_of_readyO {z : ℕ} (h : readyO F dL z = true) : stReady F dL z = true := by
  rw [stReady]
  split
  · exact readyO_readyE F dL h
  · exact h

/-! ### The bounded case: the machine gets stuck on some requirement -/

section Bounded

variable (L : ℕ → Bool)

/-- If the gap function is bounded it is eventually constant, and the machine is then stuck on
one requirement, having just reset its candidate counter. -/
theorem bounded_stabilizes (hb : ∃ B, ∀ n, fF F vIdx dL n ≤ B) :
    ∃ n₀ c, (∀ n, n₀ ≤ n → prC (stateAt F vIdx dL n) = c) ∧
      (∀ n, n₀ ≤ n → jmp F vIdx dL n = false) ∧ prS (stateAt F vIdx dL n₀) = 0 := by
  classical
  obtain ⟨B, hB⟩ := hb
  set S : Set ℕ := Set.range (fF F vIdx dL) with hS
  have hne : S.Nonempty := ⟨fF F vIdx dL 0, ⟨0, rfl⟩⟩
  have hbdd : BddAbove S := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
  obtain ⟨m, hm⟩ := hmem
  set c := sSup S with hc
  have hex : ∃ n, fF F vIdx dL n = c := ⟨m, hm⟩
  set n₀ := Nat.find hex with hn₀
  have hfn₀ : fF F vIdx dL n₀ = c := Nat.find_spec hex
  have hconst : ∀ n, n₀ ≤ n → fF F vIdx dL n = c := by
    intro n hn
    have h1 : fF F vIdx dL n₀ ≤ fF F vIdx dL n := fF_mono F vIdx dL hn
    have h2 : fF F vIdx dL n ≤ c := le_csSup hbdd ⟨n, rfl⟩
    omega
  refine ⟨n₀, c, fun n hn => hconst n hn, fun n hn => ?_, ?_⟩
  · have h1 := hconst n hn
    have h2 := hconst (n + 1) (by omega)
    have := fF_succ F vIdx dL n
    by_cases hj : jmp F vIdx dL n = true
    · rw [hj] at this; simp at this; omega
    · simpa using hj
  · rcases Nat.eq_zero_or_pos n₀ with h | h
    · rw [h]; simp [stateAt, s0]
    · obtain ⟨k, hk⟩ : ∃ k, n₀ = k + 1 := ⟨n₀ - 1, by omega⟩
      have hlt : fF F vIdx dL k ≠ c := by
        rw [hn₀] at hk
        exact Nat.find_min hex (by omega)
      have hjk : jmp F vIdx dL k = true := by
        have := fF_succ F vIdx dL k
        rw [← hk, hfn₀] at this
        by_cases hj : jmp F vIdx dL k = true
        · exact hj
        · rw [if_neg (by simpa using hj)] at this; omega
      rw [hk, stateAt_succ, step_prS]
      rw [jmp] at hjk
      simp at hjk
      simp [hjk.1, hjk.2]

/-- While no test is affordable, the candidate counter does not move. -/
theorem prS_stable (n m : ℕ) (hnm : n ≤ m)
    (h : ∀ k, n ≤ k → k < m → stReady F dL (stateAt F vIdx dL k) = false) :
    prS (stateAt F vIdx dL m) = prS (stateAt F vIdx dL n) := by
  induction m with
  | zero =>
      have : n = 0 := by omega
      rw [this]
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h1 | h1
      · have hm : n ≤ m := by omega
        have hstep : prS (stateAt F vIdx dL (m + 1)) = prS (stateAt F vIdx dL m) := by
          rw [stateAt_succ, step_prS, if_neg (by simp [h m hm (by omega)])]
        rw [hstep]
        exact ih hm (fun k hk hkm => h k hk (by omega))
      · have : n = m + 1 := by omega
        rw [this]

/-- If the machine is stuck on one requirement, some test is nevertheless affordable from any
time on. -/
theorem exists_ready (n₀ c : ℕ) (hstab : ∀ n, n₀ ≤ n → prC (stateAt F vIdx dL n) = c)
    (n : ℕ) (hn : n₀ ≤ n) :
    ∃ m, n ≤ m ∧ stReady F dL (stateAt F vIdx dL m) = true := by
  by_contra hcon
  push_neg at hcon
  have hfalse : ∀ m, n ≤ m → stReady F dL (stateAt F vIdx dL m) = false := by
    intro m hm
    simpa using hcon m hm
  have hS : ∀ m, n ≤ m → prS (stateAt F vIdx dL m) = prS (stateAt F vIdx dL n) := by
    intro m hm
    exact prS_stable F vIdx dL n m hm (fun k hk _ => hfalse k hk)
  obtain ⟨N, hN⟩ := eventually_readyO F dL c (prS (stateAt F vIdx dL n))
  have hmax : n ≤ max N n := le_max_right _ _
  have hrO := hN (max N n) (le_max_left _ _) (stateAt F vIdx dL (max N n))
    (hstab _ (le_trans hn hmax)) (hS _ hmax) (inv_P F vIdx dL _)
  have := stReady_of_readyO F dL hrO
  rw [hfalse _ hmax] at this
  exact absurd this (by simp)

theorem ready_with_same_S (n₀ c : ℕ) (hstab : ∀ n, n₀ ≤ n → prC (stateAt F vIdx dL n) = c)
    (n : ℕ) (hn : n₀ ≤ n) :
    ∃ m, n ≤ m ∧ stReady F dL (stateAt F vIdx dL m) = true ∧
      prS (stateAt F vIdx dL m) = prS (stateAt F vIdx dL n) := by
  classical
  obtain ⟨m0, hm0, hr0⟩ := exists_ready F vIdx dL n₀ c hstab n hn
  have hex : ∃ k, stReady F dL (stateAt F vIdx dL (n + k)) = true :=
    ⟨m0 - n, by rwa [Nat.add_sub_cancel' hm0]⟩
  refine ⟨n + Nat.find hex, by omega, Nat.find_spec hex, ?_⟩
  refine prS_stable F vIdx dL n (n + Nat.find hex) (by omega) ?_
  intro j hj hjk
  have hlt : j - n < Nat.find hex := by omega
  have := Nat.find_min hex hlt
  rw [Nat.add_sub_cancel' hj] at this
  simpa using this

/-- If the machine is stuck on one requirement, every candidate is eventually tested. -/
theorem candidate_tested (n₀ c : ℕ) (hstab : ∀ n, n₀ ≤ n → prC (stateAt F vIdx dL n) = c)
    (hnoj : ∀ n, n₀ ≤ n → jmp F vIdx dL n = false) (hs0 : prS (stateAt F vIdx dL n₀) = 0) :
    ∀ x, ∃ n, n₀ ≤ n ∧ prS (stateAt F vIdx dL n) = x ∧
      stReady F dL (stateAt F vIdx dL n) = true := by
  intro x
  induction x with
  | zero =>
      obtain ⟨m, hm, hr, hS⟩ := ready_with_same_S F vIdx dL n₀ c hstab n₀ le_rfl
      exact ⟨m, le_trans le_rfl hm, by rw [hS, hs0], hr⟩
  | succ x ih =>
      obtain ⟨n, hn, hSn, hr⟩ := ih
      have hw : stWitness F vIdx (stateAt F vIdx dL n) = false := by
        have := hnoj n hn
        rw [jmp, hr] at this
        simpa using this
      have hnext : prS (stateAt F vIdx dL (n + 1)) = x + 1 := by
        rw [stateAt_succ, step_prS, if_pos hr, if_neg (by simp [hw]), hSn]
      obtain ⟨m, hm, hr', hS'⟩ := ready_with_same_S F vIdx dL n₀ c hstab (n + 1) (by omega)
      exact ⟨m, by omega, by rw [hS', hnext], hr'⟩

/-- If the machine gets stuck on an even requirement, the corresponding program decides the
diagonal language. -/
theorem stuck_even (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (n₀ c : ℕ) (hstab : ∀ n, n₀ ≤ n → prC (stateAt F vIdx dL n) = c)
    (hnoj : ∀ n, n₀ ≤ n → jmp F vIdx dL n = false) (hs0 : prS (stateAt F vIdx dL n₀) = 0)
    (hpar : c % 2 = 0) :
    ∀ x, Adiag F vIdx dL L x = decide (F.Red (c / 2) x = 1) := by
  intro x
  obtain ⟨n, hn, hSn, hr⟩ := candidate_tested F vIdx dL n₀ c hstab hnoj hs0 x
  have hcn : prC (stateAt F vIdx dL n) = c := hstab n hn
  have hpar' : prC (stateAt F vIdx dL n) % 2 = 0 := by rw [hcn]; exact hpar
  have hrE : readyE F dL (stateAt F vIdx dL n) = true := by
    rw [stReady, if_pos hpar'] at hr; exact hr
  have hw : stWitness F vIdx (stateAt F vIdx dL n) = false := by
    have := hnoj n hn
    rw [jmp, hr] at this
    simpa using this
  rw [stWitness_even F vIdx dL L hcert hLdef n hpar' hrE, hSn, hcn] at hw
  revert hw
  cases hd : decide (F.Red (c / 2) x = 1) <;> cases hA : Adiag F vIdx dL L x <;> simp

/-- If the machine gets stuck on an odd requirement, the corresponding program is a reduction
of `L` to the diagonal language. -/
theorem stuck_odd (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (n₀ c : ℕ) (hstab : ∀ n, n₀ ≤ n → prC (stateAt F vIdx dL n) = c)
    (hnoj : ∀ n, n₀ ≤ n → jmp F vIdx dL n = false) (hs0 : prS (stateAt F vIdx dL n₀) = 0)
    (hpar : c % 2 ≠ 0) :
    ∀ x, L x = Adiag F vIdx dL L (F.Red (c / 2) x) := by
  intro x
  obtain ⟨n, hn, hSn, hr⟩ := candidate_tested F vIdx dL n₀ c hstab hnoj hs0 x
  have hcn : prC (stateAt F vIdx dL n) = c := hstab n hn
  have hpar' : prC (stateAt F vIdx dL n) % 2 ≠ 0 := by rw [hcn]; exact hpar
  have hrO : readyO F dL (stateAt F vIdx dL n) = true := by
    rw [stReady, if_neg hpar'] at hr; exact hr
  have hw : stWitness F vIdx (stateAt F vIdx dL n) = false := by
    have := hnoj n hn
    rw [jmp, hr] at this
    simpa using this
  rw [stWitness_odd F vIdx dL L hcert hLdef n hpar' hrO, hSn, hcn] at hw
  revert hw
  cases hd : L x <;> cases hA : Adiag F vIdx dL L (F.Red (c / 2) x) <;> simp

end Bounded

/-! ### The unbounded case: every requirement is met -/

theorem unbounded_stage (hunb : ∀ B, ∃ n, B < fF F vIdx dL n) (c : ℕ) :
    ∃ n, prC (stateAt F vIdx dL n) = c ∧ stReady F dL (stateAt F vIdx dL n) = true ∧
      stWitness F vIdx (stateAt F vIdx dL n) = true := by
  classical
  have hex : ∃ n, c < fF F vIdx dL n := hunb c
  set m := Nat.find hex with hm
  have hspec : c < fF F vIdx dL m := Nat.find_spec hex
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, fF_zero] at hspec; omega
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hkle : ¬ (c < fF F vIdx dL k) := Nat.find_min hex (by omega)
  have hsucc := fF_succ F vIdx dL k
  rw [← hk] at hsucc
  have hjk : jmp F vIdx dL k = true := by
    by_cases hj : jmp F vIdx dL k = true
    · exact hj
    · rw [if_neg (by simpa using hj)] at hsucc; omega
  rw [hjk] at hsucc
  simp only [if_pos] at hsucc
  have hfk : fF F vIdx dL k = c := by omega
  rw [jmp] at hjk
  simp only [Bool.and_eq_true] at hjk
  exact ⟨k, hfk, hjk.1, hjk.2⟩

/-! ### The diagonal language is in `NP` -/

theorem Adiag_NP (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1) :
    NPLang F (Adiag F vIdx dL L) := by
  refine ⟨fun z => decide (F.Red vIdx z = 1) &&
      decide (fF F vIdx dL (Nat.size (Nat.unpair z).1) % 2 = 0), dL, ?_, ?_, ?_⟩
  · have h1 : PFb F (fun z => decide (F.Red vIdx z = 1)) :=
      pfb_eq F (pf_Red F vIdx) (pf_const F 1)
    have h2 : PFb F (fun z => decide (fF F vIdx dL (Nat.size (Nat.unpair z).1) % 2 = 0)) :=
      pfb_comp F (pfb_even_fF F vIdx dL) F.mem_fst
    exact pfb_and F h1 h2
  · intro x y hxy
    simp only [Nat.unpair_pair, Bool.and_eq_true, decide_eq_true_eq] at hxy
    exact hcert x y hxy.1
  · intro x
    simp only [Nat.unpair_pair, Adiag, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hL, hp⟩
      obtain ⟨y, hy⟩ := (hLdef x).mp hL
      exact ⟨y, hy, hp⟩
    · rintro ⟨y, hy, hp⟩
      exact ⟨(hLdef x).mpr ⟨y, hy⟩, hp⟩

/-! ### Putting the two cases together -/

theorem size_le_size_of_le {a b : ℕ} (h : a ≤ b) : Nat.size a ≤ Nat.size b :=
  Nat.size_le_size h

/-- If the gap function is bounded, then `L` itself is polynomial time, contradicting the
choice of `L`. -/
theorem PLang_of_bounded (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (hb : ∃ B, ∀ n, fF F vIdx dL n ≤ B) : PLang F L := by
  obtain ⟨n₀, c, hstab, hnoj, hs0⟩ := bounded_stabilizes F vIdx dL hb
  have hsz : ∀ x, 2 ^ n₀ ≤ x → n₀ ≤ Nat.size x := by
    intro x hx
    have := size_le_size_of_le hx
    rw [Nat.size_pow] at this
    omega
  by_cases hpar : c % 2 = 0
  · have hAe := stuck_even F vIdx dL L hcert hLdef n₀ c hstab hnoj hs0 hpar
    have hPA : PLang F (Adiag F vIdx dL L) := (PLang_iff_Mach F _).mpr ⟨c / 2, hAe⟩
    refine PLang_of_eventually_eq F (2 ^ n₀) (Adiag F vIdx dL L) L hPA ?_
    intro x hx
    have hfx : fF F vIdx dL (Nat.size x) = c := hstab _ (hsz x hx)
    rw [Adiag, hfx, hpar]
    simp
  · have hAo := stuck_odd F vIdx dL L hcert hLdef n₀ c hstab hnoj hs0 hpar
    set T : ℕ → Bool := fun y => if y < 2 ^ n₀ then Adiag F vIdx dL L y else false with hT
    have hPT : PLang F T := by
      refine PLang_of_eventually_eq F (2 ^ n₀) (fun _ => false) T ?_ ?_
      · exact pf_congr (pf_const F 0) (by funext x; simp)
      · intro x hx
        simp [hT, Nat.not_lt.mpr hx]
    have hLT : ∀ x, L x = T (F.Red (c / 2) x) := by
      intro x
      rw [hAo x]
      by_cases hlt : F.Red (c / 2) x < 2 ^ n₀
      · simp [hT, hlt]
      · have hfx : fF F vIdx dL (Nat.size (F.Red (c / 2) x)) = c :=
          hstab _ (hsz _ (by omega))
        simp [hT, hlt, Adiag, hfx, hpar]
    have hcomp : PF F (fun x => if T (F.Red (c / 2) x) then 1 else 0) :=
      pf_comp F hPT (pf_Red F (c / 2))
    exact pf_congr hcomp (by funext x; rw [hLT x])

/-- If the gap function is unbounded, the diagonal language is not polynomial time. -/
theorem not_PLang_Adiag (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (hunb : ∀ B, ∃ n, B < fF F vIdx dL n) : ¬ PLang F (Adiag F vIdx dL L) := by
  intro hP
  obtain ⟨e, he⟩ := (PLang_iff_Mach F _).mp hP
  obtain ⟨n, hcn, hr, hw⟩ := unbounded_stage F vIdx dL hunb (2 * e)
  have hpar : prC (stateAt F vIdx dL n) % 2 = 0 := by rw [hcn]; omega
  have hrE : readyE F dL (stateAt F vIdx dL n) = true := by
    rw [stReady, if_pos hpar] at hr; exact hr
  have hdiv : prC (stateAt F vIdx dL n) / 2 = e := by rw [hcn]; omega
  rw [stWitness_even F vIdx dL L hcert hLdef n hpar hrE, hdiv,
    he (prS (stateAt F vIdx dL n))] at hw
  simp at hw

/-- If the gap function is unbounded, `L` does not reduce to the diagonal language. -/
theorem not_reduces_Adiag (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (hunb : ∀ B, ∃ n, B < fF F vIdx dL n) : ¬ PolyReduces F L (Adiag F vIdx dL L) := by
  rintro ⟨g, ⟨e, rfl⟩, hg⟩
  obtain ⟨n, hcn, hr, hw⟩ := unbounded_stage F vIdx dL hunb (2 * e + 1)
  have hpar : prC (stateAt F vIdx dL n) % 2 ≠ 0 := by rw [hcn]; omega
  have hrO : readyO F dL (stateAt F vIdx dL n) = true := by
    rw [stReady, if_neg hpar] at hr; exact hr
  have hdiv : prC (stateAt F vIdx dL n) / 2 = e := by rw [hcn]; omega
  rw [stWitness_odd F vIdx dL L hcert hLdef n hpar hrO, hdiv,
    ← hg (prS (stateAt F vIdx dL n))] at hw
  simp at hw

end Ladner

/-- **Ladner's theorem**.  In any model of polynomial time computation, if `P ≠ NP` — that is,
if some language is in `NP` but not in `P` — then there is an *`NP`-intermediate* language:
a language which lies in `NP`, is not in `P`, and is not `NP`-complete. -/
theorem CS.ladner (F : Ladner.PolyFramework)
    (hPNP : ∃ L : ℕ → Bool, Ladner.NPLang F L ∧ ¬ Ladner.PLang F L) :
    ∃ A : ℕ → Bool, Ladner.NPLang F A ∧ ¬ Ladner.PLang F A ∧ ¬ Ladner.NPComplete F A := by
  classical
  obtain ⟨L, hLNP, hLnotP⟩ := hPNP
  obtain ⟨V, d, hV, hcert0, hdef0⟩ := hLNP
  obtain ⟨vIdx, hvIdx⟩ := (Ladner.PLang_iff_Mach F V).mp hV
  have hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ d) := by
    intro x y h
    exact hcert0 x y (by rw [hvIdx]; simp [h])
  have hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1 := by
    intro x
    rw [hdef0 x]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hvIdx] at hy; simpa using hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hvIdx]; simp [hy]⟩
  have hunb : ∀ B, ∃ n, B < Ladner.fF F vIdx d n := by
    intro B
    by_contra hcon
    push_neg at hcon
    exact hLnotP (Ladner.PLang_of_bounded F vIdx d L hcert hLdef ⟨B, hcon⟩)
  refine ⟨Ladner.Adiag F vIdx d L, Ladner.Adiag_NP F vIdx d L hcert hLdef,
    Ladner.not_PLang_Adiag F vIdx d L hcert hLdef hunb, ?_⟩
  rintro ⟨-, hcomplete⟩
  exact Ladner.not_reduces_Adiag F vIdx d L hcert hLdef hunb
    (hcomplete L ⟨V, d, hV, hcert0, hdef0⟩)

#print axioms CS.ladner

