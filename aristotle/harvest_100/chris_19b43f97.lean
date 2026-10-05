/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Interp

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
`NSPACE f ⊆ DSPACE (16 * (f + 1)^2)`, i.e. Savitch's theorem, and the corollary
`PSPACE = NPSPACE`.

The model of computation is set up in `RequestProject.Savitch.Model`: a device is
a configuration graph with read-only access to the input tape, and the space it
uses is the number of bits needed to encode a configuration.

The proof follows the classical argument.  Given a nondeterministic device `M`
using `s` bits of space, its configuration graph (extended by a single absorbing
accepting vertex) has at most `2 ^ (s+1)` vertices, so acceptance amounts to
reachability in a graph of that size.  Reachability is computed deterministically
by the midpoint recursion `reach` of `RequestProject.Savitch.Reach`, of depth
`K = s + 1`, and this recursion is executed by the explicit stack machine of
`RequestProject.Savitch.Interp`, whose states consist of at most `K` frames, each
holding three vertices and a bit.  That machine therefore has at most
`2 ^ (16 * K ^ 2)` configurations, i.e. it runs in space `O(s²)`.
-/

namespace CS

/-! ### Counting the states of the evaluator -/

section Card

variable {C : Type} [Fintype C] (K : ℕ)

/-- Encoding of a state of the evaluator by its mode and the (padded) list of its
frames. -/
def stEnc (p : St C) : Mode C × (Fin K → Option (Frame C)) :=
  (p.1, fun i => p.2[(i : ℕ)]?)

omit [Fintype C] in
lemma stEnc_inj {p q : St C} (hp : p.2.length ≤ K) (hq : q.2.length ≤ K)
    (h : stEnc K p = stEnc K q) : p = q := by
  obtain ⟨m, l⟩ := p
  obtain ⟨m', l'⟩ := q
  have hp' : l.length ≤ K := hp
  have hq' : l'.length ≤ K := hq
  have h1 : m = m' := congrArg Prod.fst h
  have h2 : ∀ i : Fin K, l[(i : ℕ)]? = l'[(i : ℕ)]? := fun i => congrFun (congrArg Prod.snd h) i
  refine Prod.ext h1 ?_
  apply List.ext_getElem?
  intro i
  by_cases hi : i < K
  · exact h2 ⟨i, hi⟩
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- The states of the evaluator with at most `K` frames. -/
noncomputable instance instFintypeBoundedSt : Fintype { p : St C // p.2.length ≤ K } :=
  Fintype.ofInjective (fun p => stEnc K p.1)
    (fun p q h => Subtype.ext (stEnc_inj K p.2 q.2 h))

lemma card_mode : Fintype.card (Mode C) = Fintype.card C * Fintype.card C + 2 := by
  rw [Fintype.card_congr (modeEquiv C)]
  simp [Fintype.card_sum, Fintype.card_prod]

lemma card_frame : Fintype.card (Frame C) = Fintype.card C ^ 3 * 2 := by
  rw [Fintype.card_congr (frameEquiv C)]
  simp [Fintype.card_prod]
  ring

lemma card_boundedSt_le :
    Fintype.card { p : St C // p.2.length ≤ K } ≤
      (Fintype.card C * Fintype.card C + 2) * (Fintype.card C ^ 3 * 2 + 1) ^ K := by
  have h := Fintype.card_le_of_injective (fun p : { p : St C // p.2.length ≤ K } => stEnc K p.1)
    (fun p q h => Subtype.ext (stEnc_inj K p.2 q.2 h))
  refine h.trans ?_
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_option, card_mode, card_frame,
    Fintype.card_fin]

/-- The evaluator uses `O(K²)` bits of space. -/
lemma card_boundedSt_le_pow (hcard : Fintype.card C ≤ 2 ^ K) (hK : 1 ≤ K) :
    Fintype.card { p : St C // p.2.length ≤ K } ≤ 2 ^ (16 * K ^ 2) := by
  set N := Fintype.card C with hN
  have h1 : N * N + 2 ≤ 2 ^ (2 * K + 1) := by
    have hNN : N * N ≤ 2 ^ K * 2 ^ K := Nat.mul_le_mul hcard hcard
    have : (2 : ℕ) ^ K * 2 ^ K = 2 ^ (2 * K) := by ring
    have h2K : (2 : ℕ) ^ 1 ≤ 2 ^ (2 * K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ (2 * K + 1) = 2 ^ (2 * K) + 2 ^ (2 * K) := by ring
    omega
  have h2 : N ^ 3 * 2 + 1 ≤ 2 ^ (3 * K + 2) := by
    have hN3 : N ^ 3 ≤ (2 ^ K) ^ 3 := Nat.pow_le_pow_left hcard 3
    have he : ((2 : ℕ) ^ K) ^ 3 = 2 ^ (3 * K) := by rw [← pow_mul]; ring_nf
    have h1K : (1 : ℕ) ≤ 2 ^ (3 * K) := Nat.one_le_two_pow
    have : (2 : ℕ) ^ (3 * K + 2) = 2 ^ (3 * K) * 4 := by ring
    omega
  have h3 : (N ^ 3 * 2 + 1) ^ K ≤ (2 ^ (3 * K + 2)) ^ K := Nat.pow_le_pow_left h2 K
  have h4 : Fintype.card { p : St C // p.2.length ≤ K } ≤ 2 ^ (2 * K + 1) * (2 ^ (3 * K + 2)) ^ K :=
    (card_boundedSt_le K).trans (Nat.mul_le_mul h1 h3)
  refine h4.trans ?_
  rw [← pow_mul, ← pow_add]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  nlinarith [sq_nonneg K, hK]

end Card

/-! ### Adding a unique accepting configuration -/

section Lift

variable {Γ : Type} (M : NDevice Γ)

/-- Input head position, on the configuration space extended by a sink. -/
def liftHead : Option M.Conf → ℕ
  | some a => M.head a
  | none => 0

/-- The transition relation of `M`, extended by a fresh absorbing vertex `none`
which is entered exactly from the accepting configurations. -/
def liftStep (σ : Option Γ) : Option M.Conf → Option M.Conf → Prop
  | some a, some b => M.step a σ b
  | some a, none => M.acc a
  | none, _ => False

/-- The extended configuration graph on a concrete input `x`. -/
def liftRel (x : List Γ) (a b : Option M.Conf) : Prop :=
  liftStep M x[liftHead M a]? a b

lemma lift_up {x : List Γ} {a b : M.Conf} (h : Relation.ReflTransGen (M.stepOn x) a b) :
    Relation.ReflTransGen (liftRel M x) (some a) (some b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail hbc

lemma lift_down {x : List Γ} {a : M.Conf} {c : Option M.Conf}
    (h : Relation.ReflTransGen (liftRel M x) (some a) c) :
    (∀ b, c = some b → Relation.ReflTransGen (M.stepOn x) a b) ∧
      (c = none → ∃ b, Relation.ReflTransGen (M.stepOn x) a b ∧ M.acc b) := by
  induction h with
  | refl =>
      refine ⟨fun b hb => ?_, fun hb => ?_⟩
      · cases hb; exact Relation.ReflTransGen.refl
      · exact absurd hb (by simp)
  | @tail c d _ hcd ih =>
      cases c with
      | none => exact absurd hcd (by simp [liftRel, liftStep])
      | some c' =>
          have hpath : Relation.ReflTransGen (M.stepOn x) a c' := ih.1 c' rfl
          cases d with
          | none =>
              refine ⟨fun b hb => absurd hb (by simp), fun _ => ⟨c', hpath, ?_⟩⟩
              exact hcd
          | some d' =>
              refine ⟨fun b hb => ?_, fun hb => absurd hb (by simp)⟩
              cases hb
              exact hpath.tail hcd

/-- Acceptance of `M` is reachability of the sink in the extended graph. -/
lemma accepts_iff_reflTransGen (x : List Γ) :
    M.Accepts x ↔ Relation.ReflTransGen (liftRel M x) (some M.init) none := by
  constructor
  · rintro ⟨c, hpath, hacc⟩
    exact (lift_up M hpath).tail hacc
  · intro h
    obtain ⟨b, hpath, hacc⟩ := (lift_down M h).2 rfl
    exact ⟨b, hpath, hacc⟩

end Lift

/-! ### The deterministic simulator -/

section Device

variable {Γ : Type} (M : NDevice Γ) [Fintype M.Conf] (K : ℕ)

/-- One step of the evaluator of Savitch's recursion for `M`, when the symbol
scanned on the input tape is `σ`. -/
noncomputable def savitchStep (σ : Option Γ) : St (Option M.Conf) → St (Option M.Conf) :=
  istep K (fun a b => bdec (a = b ∨ liftStep M σ a b))

/-- The deterministic device simulating `M` : it evaluates `reach _ K` for the
extended configuration graph of `M`. -/
noncomputable def savitchDevice : DDevice Γ where
  Conf := { p : St (Option M.Conf) // p.2.length ≤ K }
  head p := ihead (liftHead M) p.1
  step p σ := ⟨savitchStep M K σ p.1, istep_length_le K _ p.1 p.2⟩
  init := ⟨(Mode.ask (some M.init) none, []), by simp⟩
  acc p := p.1 = (Mode.ret true, [])

/-- The step function of the simulator, as a function of states only (the scanned
symbol is determined by the state). -/
noncomputable def savitchRun (x : List Γ) : St (Option M.Conf) → St (Option M.Conf) :=
  fun p => savitchStep M K x[ihead (liftHead M) p]? p

lemma savitchDevice_run_val (x : List Γ) (t : ℕ) :
    ((savitchDevice M K).run x t).1 =
      (savitchRun M K x)^[t] (Mode.ask (some M.init) none, []) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ← ih, DDevice.run]
      rfl

lemma isInterp_savitchRun (x : List Γ) :
    IsInterp K (liftRel M x) (savitchRun M K x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b st hst
    unfold savitchRun savitchStep
    rw [istep_ask, if_pos hst]
    rfl
  · intro a b st hst
    unfold savitchRun savitchStep
    rw [istep_ask, if_neg hst]
  · intro v
    unfold savitchRun savitchStep
    rw [istep_ret_nil]
  · intro v fr st
    unfold savitchRun savitchStep
    rw [istep_ret_cons]

/-- **The simulator is correct.** -/
theorem savitchDevice_accepts_iff (x : List Γ)
    (hcard : Fintype.card (Option M.Conf) ≤ 2 ^ K) :
    (savitchDevice M K).Accepts x ↔ M.Accepts x := by
  have h1 : (savitchDevice M K).Accepts x ↔
      Reaches (savitchRun M K x) (Mode.ask (some M.init) none, []) (Mode.ret true, []) := by
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [← savitchDevice_run_val M K x t]
      exact ht
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      show ((savitchDevice M K).run x t).1 = (Mode.ret true, [])
      rw [savitchDevice_run_val M K x t]
      exact ht
  rw [h1, interp_accepts_iff (isInterp_savitchRun M K x), reach_iff hcard,
    ← accepts_iff_reflTransGen]

/-- **The simulator runs in space `O(K²)`.** -/
theorem savitchDevice_space (hcard : Fintype.card (Option M.Conf) ≤ 2 ^ K) (hK : 1 ≤ K) :
    (savitchDevice M K).SpaceBound (16 * K ^ 2) := by
  have hcard2 : Fintype.card { p : St (Option M.Conf) // p.2.length ≤ K } ≤
      Fintype.card (Fin (16 * K ^ 2) → Bool) := by
    have := card_boundedSt_le_pow (C := Option M.Conf) K hcard hK
    simpa using this
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard2
  exact ⟨g, g.injective⟩

end Device

/-! ### Savitch's theorem -/

/-- **Savitch's theorem**: every language recognised by a nondeterministic device
in space `f` is recognised by a deterministic device in space `O(f²)`, namely
`16 * (f + 1)²`. -/
theorem savitch (Γ : Type) (f : ℕ → ℕ) :
    NSPACE Γ f ⊆ DSPACE Γ (fun n => 16 * (f n + 1) ^ 2) := by
  rintro L ⟨M, hspace, hdec⟩
  have hfin : ∀ n, Finite (M n).Conf := by
    intro n
    obtain ⟨e, he⟩ := hspace n
    exact Finite.of_injective e he
  letI finst : ∀ n, Fintype (M n).Conf := fun n => @Fintype.ofFinite _ (hfin n)
  have hcard : ∀ n, Fintype.card (Option (M n).Conf) ≤ 2 ^ (f n + 1) := by
    intro n
    obtain ⟨e, he⟩ := hspace n
    have h1 : Fintype.card (M n).Conf ≤ 2 ^ f n := by
      have := Fintype.card_le_of_injective e he
      simpa using this
    have h2 : Fintype.card (Option (M n).Conf) = Fintype.card (M n).Conf + 1 :=
      Fintype.card_option
    have h3 : (2 : ℕ) ^ (f n + 1) = 2 ^ f n + 2 ^ f n := by ring
    have h4 : (1 : ℕ) ≤ 2 ^ f n := Nat.one_le_two_pow
    omega
  refine ⟨fun n => savitchDevice (M n) (f n + 1), fun n => ?_, fun x => ?_⟩
  · exact savitchDevice_space (M n) (f n + 1) (hcard n) (by omega)
  · rw [hdec x]
    exact (savitchDevice_accepts_iff (M x.length) (f x.length + 1) x (hcard x.length)).symm

/-! ### PSPACE = NPSPACE -/

/-- A polynomially bounded space function. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

/-- Deterministic polynomial space. -/
def PSPACE (Γ : Type) : Set (Language Γ) := {L | ∃ f, PolyBounded f ∧ L ∈ DSPACE Γ f}

/-- Nondeterministic polynomial space. -/
def NPSPACE (Γ : Type) : Set (Language Γ) := {L | ∃ f, PolyBounded f ∧ L ∈ NSPACE Γ f}

/-- A deterministic device, viewed as a nondeterministic one. -/
def DDevice.toNDevice {Γ : Type} (M : DDevice Γ) : NDevice Γ where
  Conf := M.Conf
  head := M.head
  step a σ b := M.step a σ = b
  init := M.init
  acc := M.acc

lemma DDevice.toNDevice_run {Γ : Type} (M : DDevice Γ) (x : List Γ) {c : M.Conf}
    (h : Relation.ReflTransGen (M.toNDevice.stepOn x) M.init c) : ∃ t, M.run x t = c := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨t + 1, by rw [DDevice.run, ht]; exact hbc⟩

lemma DDevice.toNDevice_accepts_iff {Γ : Type} (M : DDevice Γ) (x : List Γ) :
    M.toNDevice.Accepts x ↔ M.Accepts x := by
  constructor
  · rintro ⟨c, hpath, hacc⟩
    obtain ⟨t, ht⟩ := M.toNDevice_run x hpath
    exact ⟨t, ht ▸ hacc⟩
  · rintro ⟨t, hacc⟩
    refine ⟨M.run x t, ?_, hacc⟩
    clear hacc
    induction t with
    | zero => exact Relation.ReflTransGen.refl
    | succ t ih => exact ih.tail (by rfl)

lemma DSPACE_subset_NSPACE (Γ : Type) (f : ℕ → ℕ) : DSPACE Γ f ⊆ NSPACE Γ f := by
  rintro L ⟨M, hspace, hdec⟩
  refine ⟨fun n => (M n).toNDevice, fun n => ?_, fun x => ?_⟩
  · obtain ⟨e, he⟩ := hspace n
    exact ⟨e, he⟩
  · rw [hdec x, DDevice.toNDevice_accepts_iff]

lemma PolyBounded.savitch {f : ℕ → ℕ} (hf : PolyBounded f) :
    PolyBounded (fun n => 16 * (f n + 1) ^ 2) := by
  obtain ⟨c, k, hc⟩ := hf
  refine ⟨16 * (c + 1) ^ 2, 2 * k, fun n => ?_⟩
  have h2 : (1 : ℕ) ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h1 : f n + 1 ≤ (c + 1) * (n + 1) ^ k :=
    calc f n + 1 ≤ c * (n + 1) ^ k + 1 := Nat.add_le_add_right (hc n) 1
      _ ≤ c * (n + 1) ^ k + (n + 1) ^ k := Nat.add_le_add_left h2 _
      _ = (c + 1) * (n + 1) ^ k := by ring
  calc 16 * (f n + 1) ^ 2 ≤ 16 * ((c + 1) * (n + 1) ^ k) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
    _ = 16 * (c + 1) ^ 2 * (n + 1) ^ (2 * k) := by
        rw [mul_pow, ← pow_mul]
        ring

/-- **`PSPACE = NPSPACE`**, an immediate corollary of Savitch's theorem. -/
theorem pspace_eq_npspace (Γ : Type) : PSPACE Γ = NPSPACE Γ := by
  ext L
  constructor
  · rintro ⟨f, hf, hL⟩
    exact ⟨f, hf, DSPACE_subset_NSPACE Γ f hL⟩
  · rintro ⟨f, hf, hL⟩
    exact ⟨fun n => 16 * (f n + 1) ^ 2, hf.savitch, savitch Γ f hL⟩


/-! ### A sanity check: the model is not degenerate

The definitions above do define a nontrivial notion of computation.  For
instance, the language of nonempty words is decided in constant space, while a
device with `0` bits of space has a single configuration and hence accepts either
every word or none. -/

/-- A device accepting exactly the nonempty words. -/
def nonemptyDevice (Γ : Type) : DDevice Γ where
  Conf := Bool
  head _ := 0
  step c σ := match σ with | none => c | some _ => true
  init := false
  acc c := c = true

theorem nonempty_mem_dspace (Γ : Type) :
    (fun x : List Γ => x ≠ []) ∈ DSPACE Γ (fun _ => 1) := by
  refine ⟨fun _ => nonemptyDevice Γ, fun n => ⟨fun b _ => b, ?_⟩, fun x => ?_⟩
  · intro a b h
    simpa using congrFun h 0
  · constructor
    · intro hx
      cases x with
      | nil => exact absurd rfl hx
      | cons a t =>
          refine ⟨1, ?_⟩
          show (nonemptyDevice Γ).run (a :: t) 1 = true
          rw [DDevice.run]
          rfl
    · rintro ⟨t, ht⟩
      by_contra hx
      subst hx
      have hrun : ∀ t, (nonemptyDevice Γ).run ([] : List Γ) t = false := by
        intro t
        induction t with
        | zero => rfl
        | succ t ih => rw [DDevice.run, ih]; rfl
      rw [show ((nonemptyDevice Γ).acc ((nonemptyDevice Γ).run ([] : List Γ) t)) =
        ((nonemptyDevice Γ).run ([] : List Γ) t = true) from rfl, hrun t] at ht
      exact Bool.noConfusion ht

/-- A device with no space at all has a single configuration, so it either
accepts all words or none. -/
theorem dspace_zero_trivial {Γ : Type} (M : DDevice Γ) (h : M.SpaceBound 0)
    (x y : List Γ) (hx : M.Accepts x) : M.Accepts y := by
  obtain ⟨e, he⟩ := h
  obtain ⟨t, ht⟩ := hx
  refine ⟨0, ?_⟩
  have : M.run x t = M.init := he (funext fun i => absurd i.isLt (by omega))
  rw [this] at ht
  exact ht

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

/-
The deterministic evaluator for Savitch's recursion.

We describe a deterministic machine whose configurations are a *stack* of at most
`K` frames together with a small mode register.  The machine evaluates
`reach R K a b` by the midpoint recursion; the recursion depth is `K` and each
frame stores three vertices and one bit.  This is exactly the deterministic
`O(space²)` simulation used in Savitch's theorem.

The level of the current subgoal is not stored: it is determined by the height of
the stack (a state whose stack has height `d` is working at level `K - d`).
-/
import RequestProject.Savitch.Reach

namespace CS

/-- The mode register of the evaluator: either we have to evaluate
`reach R k a b` (at the level determined by the stack height), or we are
returning a boolean to the caller. -/
inductive Mode (C : Type) where
  | ask : C → C → Mode C
  | ret : Bool → Mode C

/-- A stack frame: we are evaluating `reach R (k+1) a b`, currently trying the
midpoint `m`; `half = false` means the first half `reach R k a m` is being
evaluated, `half = true` means the second half `reach R k m b` is. -/
structure Frame (C : Type) where
  /-- source vertex of the pending subgoal -/
  a : C
  /-- target vertex of the pending subgoal -/
  b : C
  /-- the midpoint currently being tried -/
  m : C
  /-- which half of the subgoal is being evaluated -/
  half : Bool

/-- A state of the evaluator. -/
abbrev St (C : Type) := Mode C × List (Frame C)

/-- `Mode C` is equivalent to `(C × C) ⊕ Bool`. -/
def modeEquiv (C : Type) : Mode C ≃ (C × C) ⊕ Bool where
  toFun m := match m with | .ask a b => .inl (a, b) | .ret v => .inr v
  invFun z := match z with | .inl (a, b) => .ask a b | .inr v => .ret v
  left_inv m := by cases m <;> rfl
  right_inv z := by rcases z with ⟨a, b⟩ | v <;> rfl

/-- `Frame C` is equivalent to `C × C × C × Bool`. -/
def frameEquiv (C : Type) : Frame C ≃ C × C × C × Bool where
  toFun fr := (fr.a, fr.b, fr.m, fr.half)
  invFun z := ⟨z.1, z.2.1, z.2.2.1, z.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeMode (C : Type) [Fintype C] : Fintype (Mode C) :=
  Fintype.ofEquiv _ (modeEquiv C).symm

instance instFintypeFrame (C : Type) [Fintype C] : Fintype (Frame C) :=
  Fintype.ofEquiv _ (frameEquiv C).symm

section Enum

variable (C : Type) [Fintype C] [Nonempty C]

/-- An enumeration of `C` by natural numbers (indices are read modulo the
cardinality, so that the function is total). -/
noncomputable def enum (i : ℕ) : C :=
  (Fintype.equivFin C).symm ⟨i % Fintype.card C, Nat.mod_lt _ Fintype.card_pos⟩

/-- The successor of a vertex in the enumeration, if any. -/
noncomputable def nxt (m : C) : Option C :=
  if ((Fintype.equivFin C) m : ℕ) + 1 < Fintype.card C then
    some (enum C (((Fintype.equivFin C) m : ℕ) + 1))
  else none

variable {C}

lemma idx_enum {i : ℕ} (hi : i < Fintype.card C) :
    ((Fintype.equivFin C) (enum C i) : ℕ) = i := by
  unfold enum
  rw [Equiv.apply_symm_apply]
  exact Nat.mod_eq_of_lt hi

lemma nxt_enum_some {i : ℕ} (hi : i < Fintype.card C) (h : i + 1 < Fintype.card C) :
    nxt C (enum C i) = some (enum C (i + 1)) := by
  unfold nxt
  rw [idx_enum hi, if_pos h]

lemma nxt_enum_none {i : ℕ} (hi : i < Fintype.card C) (h : ¬ i + 1 < Fintype.card C) :
    nxt C (enum C i) = none := by
  unfold nxt
  rw [idx_enum hi, if_neg h]

lemma enum_surj (m : C) : ∃ i, i < Fintype.card C ∧ enum C i = m := by
  refine ⟨((Fintype.equivFin C) m : ℕ), (Fintype.equivFin C m).isLt, ?_⟩
  unfold enum
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (Nat.mod_eq_of_lt (Fintype.equivFin C m).isLt)

end Enum

section Interp

variable {C : Type} [Fintype C] [Nonempty C]

/-- Move on to the next midpoint (or give up, if the midpoints are exhausted). -/
noncomputable def advance (fr : Frame C) (st : List (Frame C)) : St C :=
  match nxt C fr.m with
  | some m' => (Mode.ask fr.a m', ⟨fr.a, fr.b, m', false⟩ :: st)
  | none => (Mode.ret false, st)

/-- One step of the evaluator, with maximal recursion depth `K` and base-case
test `base`. -/
noncomputable def istep (K : ℕ) (base : C → C → Bool) : St C → St C
  | (Mode.ask a b, st) =>
      if st.length = K then (Mode.ret (base a b), st)
      else (Mode.ask a (enum C 0), ⟨a, b, enum C 0, false⟩ :: st)
  | (Mode.ret v, []) => (Mode.ret v, [])
  | (Mode.ret v, fr :: st) =>
      if fr.half then
        (if v then (Mode.ret true, st) else advance fr st)
      else
        (if v then (Mode.ask fr.m fr.b, ⟨fr.a, fr.b, fr.m, true⟩ :: st) else advance fr st)

/-- The input head position of a state of the evaluator. -/
def ihead (hd : C → ℕ) : St C → ℕ
  | (Mode.ask a _, _) => hd a
  | (Mode.ret _, _) => 0

@[simp] lemma istep_ask (K : ℕ) (base : C → C → Bool) (a b : C) (st : List (Frame C)) :
    istep K base (Mode.ask a b, st) =
      if st.length = K then (Mode.ret (base a b), st)
      else (Mode.ask a (enum C 0), ⟨a, b, enum C 0, false⟩ :: st) := rfl

@[simp] lemma istep_ret_nil (K : ℕ) (base : C → C → Bool) (v : Bool) :
    istep K base (Mode.ret v, ([] : List (Frame C))) = (Mode.ret v, []) := rfl

@[simp] lemma istep_ret_cons (K : ℕ) (base : C → C → Bool) (v : Bool) (fr : Frame C)
    (st : List (Frame C)) :
    istep K base (Mode.ret v, fr :: st) =
      if fr.half then
        (if v then (Mode.ret true, st) else advance fr st)
      else
        (if v then (Mode.ask fr.m fr.b, ⟨fr.a, fr.b, fr.m, true⟩ :: st) else advance fr st) := rfl

omit [Fintype C] [Nonempty C] in
@[simp] lemma ihead_ask (hd : C → ℕ) (a b : C) (st : List (Frame C)) :
    ihead hd (Mode.ask a b, st) = hd a := rfl

lemma advance_length_le {K : ℕ} (fr : Frame C) (st : List (Frame C)) (h : st.length + 1 ≤ K) :
    (advance fr st).2.length ≤ K := by
  unfold advance
  cases nxt C fr.m with
  | none => show st.length ≤ K; omega
  | some m' => show st.length + 1 ≤ K; omega

/-- The evaluator never uses more than `K` frames. -/
lemma istep_length_le (K : ℕ) (base : C → C → Bool) (p : St C) (h : p.2.length ≤ K) :
    (istep K base p).2.length ≤ K := by
  obtain ⟨mo, st⟩ := p
  have h : st.length ≤ K := h
  cases mo with
  | ask a b =>
      by_cases hl : st.length = K
      · rw [istep_ask, if_pos hl]; exact h
      · rw [istep_ask, if_neg hl]
        show st.length + 1 ≤ K
        omega
  | ret v =>
      cases st with
      | nil => rw [istep_ret_nil]; simp
      | cons fr st =>
          have hst : st.length + 1 ≤ K := h
          rw [istep_ret_cons]
          by_cases hh : fr.half
          · rw [if_pos hh]
            by_cases hv : v
            · rw [if_pos hv]; show st.length ≤ K; omega
            · rw [if_neg hv]; exact advance_length_le fr st hst
          · rw [if_neg hh]
            by_cases hv : v
            · rw [if_pos hv]; show st.length + 1 ≤ K; omega
            · rw [if_neg hv]; exact advance_length_le fr st hst

variable (K : ℕ) (R : C → C → Prop) (dstep : St C → St C)

/-- The abstract specification of one step of the evaluator: `dstep` behaves like
`istep K base` where the base-case test is the one-step reachability of `R`. -/
structure IsInterp : Prop where
  /-- at the bottom level, the machine tests `R` directly -/
  base : ∀ (a b : C) (st : List (Frame C)), st.length = K →
    dstep (Mode.ask a b, st) = (Mode.ret (reach R 0 a b), st)
  /-- above the bottom level, the machine pushes a frame with the first midpoint -/
  push : ∀ (a b : C) (st : List (Frame C)), st.length ≠ K →
    dstep (Mode.ask a b, st) = (Mode.ask a (enum C 0), ⟨a, b, enum C 0, false⟩ :: st)
  /-- returning with an empty stack: the machine halts -/
  halt : ∀ v : Bool, dstep (Mode.ret v, ([] : List (Frame C))) = (Mode.ret v, [])
  /-- returning to the caller -/
  pop : ∀ (v : Bool) (fr : Frame C) (st : List (Frame C)),
    dstep (Mode.ret v, fr :: st) =
      if fr.half then
        (if v then (Mode.ret true, st) else advance fr st)
      else
        (if v then (Mode.ask fr.m fr.b, ⟨fr.a, fr.b, fr.m, true⟩ :: st) else advance fr st)

lemma isInterp_istep (base : C → C → Bool)
    (hbase : ∀ a b : C, base a b = reach R 0 a b) : IsInterp K R (istep K base) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b st h; simp [h, hbase]
  · intro a b st h; simp [h]
  · intro v; simp
  · intro v fr st; simp

variable {K R dstep}

/-- `q` is reached from `p` after some number of steps. -/
def Reaches (dstep : St C → St C) (p q : St C) : Prop := ∃ t, dstep^[t] p = q

omit [Fintype C] [Nonempty C] in
lemma Reaches.refl (p : St C) : Reaches dstep p p := ⟨0, rfl⟩

omit [Fintype C] [Nonempty C] in
lemma Reaches.one {p q : St C} (h : dstep p = q) : Reaches dstep p q := ⟨1, by simpa using h⟩

omit [Fintype C] [Nonempty C] in
lemma Reaches.trans {p q r : St C} (h₁ : Reaches dstep p q) (h₂ : Reaches dstep q r) :
    Reaches dstep p r := by
  obtain ⟨t₁, h₁⟩ := h₁
  obtain ⟨t₂, h₂⟩ := h₂
  exact ⟨t₂ + t₁, by rw [Function.iterate_add_apply, h₁, h₂]⟩

omit [Fintype C] [Nonempty C] in
lemma Reaches.head {p q r : St C} (h : dstep p = q) (h₂ : Reaches dstep q r) :
    Reaches dstep p r := (Reaches.one h).trans h₂

/-- The set of midpoints from index `i` on witnesses the subgoal. -/
noncomputable def reachFrom (R : C → C → Prop) (k : ℕ) (a b : C) (i : ℕ) : Bool :=
  bdec (∃ j, i ≤ j ∧ j < Fintype.card C ∧
    reach R k a (enum C j) = true ∧ reach R k (enum C j) b = true)

lemma reachFrom_zero (k : ℕ) (a b : C) : reachFrom R k a b 0 = reach R (k + 1) a b := by
  unfold reachFrom
  rw [reach_succ]
  congr 1
  apply propext
  constructor
  · rintro ⟨j, -, -, h1, h2⟩
    exact ⟨enum C j, h1, h2⟩
  · rintro ⟨m, h1, h2⟩
    obtain ⟨j, hj, rfl⟩ := enum_surj m
    exact ⟨j, Nat.zero_le _, hj, h1, h2⟩

lemma reachFrom_succ_of_first_false {k : ℕ} {a b : C} {i : ℕ}
    (h : reach R k a (enum C i) = false) : reachFrom R k a b i = reachFrom R k a b (i + 1) := by
  unfold reachFrom
  congr 1
  apply propext
  constructor
  · rintro ⟨j, hij, hj, h1, h2⟩
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rw [h] at h1; exact absurd h1 (by simp)
    · exact ⟨j, hlt, hj, h1, h2⟩
  · rintro ⟨j, hij, hj, h1, h2⟩
    exact ⟨j, by omega, hj, h1, h2⟩

lemma reachFrom_succ_of_second_false {k : ℕ} {a b : C} {i : ℕ}
    (h : reach R k (enum C i) b = false) : reachFrom R k a b i = reachFrom R k a b (i + 1) := by
  unfold reachFrom
  congr 1
  apply propext
  constructor
  · rintro ⟨j, hij, hj, h1, h2⟩
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rw [h] at h2; exact absurd h2 (by simp)
    · exact ⟨j, hlt, hj, h1, h2⟩
  · rintro ⟨j, hij, hj, h1, h2⟩
    exact ⟨j, by omega, hj, h1, h2⟩

lemma reachFrom_last_false {k : ℕ} {a b : C} {i : ℕ} (hi : i < Fintype.card C)
    (hlast : ¬ i + 1 < Fintype.card C) (h : reach R k a (enum C i) = false ∨
      reach R k (enum C i) b = false) : reachFrom R k a b i = false := by
  rw [reachFrom, bdec_eq_false_iff]
  rintro ⟨j, hij, hj, h1, h2⟩
  have hji : j = i := by omega
  subst hji
  rcases h with h | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2

lemma reachFrom_true {k : ℕ} {a b : C} {i : ℕ} (hi : i < Fintype.card C)
    (h1 : reach R k a (enum C i) = true) (h2 : reach R k (enum C i) b = true) :
    reachFrom R k a b i = true := by
  rw [reachFrom, bdec_eq_true_iff]
  exact ⟨i, le_refl _, hi, h1, h2⟩

/-- Evaluating the midpoint loop. -/
lemma midEval (h : IsInterp K R dstep) {k : ℕ}
    (ihA : ∀ (st : List (Frame C)), st.length + k = K → ∀ a b : C,
      Reaches dstep (Mode.ask a b, st) (Mode.ret (reach R k a b), st)) :
    ∀ (d i : ℕ), Fintype.card C - i = d → i < Fintype.card C →
      ∀ (st : List (Frame C)), st.length + 1 + k = K → ∀ a b : C,
      Reaches dstep (Mode.ask a (enum C i), (⟨a, b, enum C i, false⟩ : Frame C) :: st)
        (Mode.ret (reachFrom R k a b i), st) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro i hdi hi st hlen a b
    set fr : Frame C := ⟨a, b, enum C i, false⟩ with hfr
    have hlen' : (fr :: st).length + k = K := by simp [List.length_cons]; omega
    have step1 : Reaches dstep (Mode.ask a (enum C i), fr :: st)
        (Mode.ret (reach R k a (enum C i)), fr :: st) := ihA (fr :: st) hlen' a (enum C i)
    -- the "advance to the next midpoint" continuation
    have advance_ok : ∀ (fr' : Frame C), fr'.a = a → fr'.b = b → fr'.m = enum C i →
        (reach R k a (enum C i) = false ∨ reach R k (enum C i) b = false) →
        Reaches dstep (advance fr' st) (Mode.ret (reachFrom R k a b i), st) := by
      intro fr' ha hb hm hfalse
      by_cases hnext : i + 1 < Fintype.card C
      · have : advance fr' st =
            (Mode.ask a (enum C (i + 1)), (⟨a, b, enum C (i + 1), false⟩ : Frame C) :: st) := by
          unfold advance
          rw [hm, nxt_enum_some hi hnext, ha, hb]
        rw [this]
        have heq : reachFrom R k a b i = reachFrom R k a b (i + 1) := by
          rcases hfalse with hf | hf
          · exact reachFrom_succ_of_first_false hf
          · exact reachFrom_succ_of_second_false hf
        rw [heq]
        exact ihd (Fintype.card C - (i + 1)) (by omega) (i + 1) rfl hnext st hlen a b
      · have : advance fr' st = (Mode.ret false, st) := by
          unfold advance
          rw [hm, nxt_enum_none hi hnext]
        rw [this, reachFrom_last_false hi hnext hfalse]
        exact Reaches.refl _
    cases hv : reach R k a (enum C i) with
    | false =>
        refine step1.trans (Reaches.head (q := advance fr st) ?_ ?_)
        · rw [hv, h.pop]
          simp [hfr]
        · exact advance_ok fr rfl rfl rfl (Or.inl hv)
    | true =>
        have step2 : Reaches dstep (Mode.ret true, fr :: st)
            (Mode.ask (enum C i) b, (⟨a, b, enum C i, true⟩ : Frame C) :: st) := by
          apply Reaches.one
          rw [h.pop]
          simp [hfr]
        set fr2 : Frame C := ⟨a, b, enum C i, true⟩ with hfr2
        have hlen2 : (fr2 :: st).length + k = K := by simp [List.length_cons]; omega
        have step3 : Reaches dstep (Mode.ask (enum C i) b, fr2 :: st)
            (Mode.ret (reach R k (enum C i) b), fr2 :: st) := ihA (fr2 :: st) hlen2 _ _
        have hchain := (((step1.trans (by rw [hv]; exact step2)).trans step3))
        cases hw : reach R k (enum C i) b with
        | false =>
            refine hchain.trans (Reaches.head (q := advance fr2 st) ?_ ?_)
            · rw [hw, h.pop]
              simp [hfr2]
            · exact advance_ok fr2 rfl rfl rfl (Or.inr hw)
        | true =>
            refine hchain.trans (Reaches.one ?_)
            rw [hw, h.pop]
            simp [hfr2, reachFrom_true hi hv hw]

/-- Evaluating a subgoal at level `k`. -/
lemma askEval (h : IsInterp K R dstep) : ∀ (k : ℕ) (st : List (Frame C)), st.length + k = K →
    ∀ a b : C, Reaches dstep (Mode.ask a b, st) (Mode.ret (reach R k a b), st) := by
  intro k
  induction k with
  | zero =>
      intro st hlen a b
      exact Reaches.one (h.base a b st (by omega))
  | succ k ih =>
      intro st hlen a b
      have hne : st.length ≠ K := by omega
      refine Reaches.head (h.push a b st hne) ?_
      have := midEval h ih (Fintype.card C - 0) 0 rfl Fintype.card_pos st (by omega) a b
      rw [reachFrom_zero] at this
      exact this

lemma iterate_halted (h : IsInterp K R dstep) (v : Bool) (t : ℕ) :
    dstep^[t] (Mode.ret v, ([] : List (Frame C))) = (Mode.ret v, []) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, h.halt, ih]

lemma halted_le (h : IsInterp K R dstep) {p : St C} {v w : Bool} {t t' : ℕ} (hle : t ≤ t')
    (ht : dstep^[t] p = (Mode.ret v, ([] : List (Frame C))))
    (ht' : dstep^[t'] p = (Mode.ret w, ([] : List (Frame C)))) : v = w := by
  have h1 : dstep^[t'] p = (Mode.ret v, ([] : List (Frame C))) := by
    rw [show t' = (t' - t) + t by omega, Function.iterate_add_apply, ht, iterate_halted h]
  rw [ht'] at h1
  have h2 := congrArg Prod.fst h1
  simpa using h2.symm

lemma halted_unique (h : IsInterp K R dstep) {p : St C} {v w : Bool} {t t' : ℕ}
    (ht : dstep^[t] p = (Mode.ret v, ([] : List (Frame C))))
    (ht' : dstep^[t'] p = (Mode.ret w, ([] : List (Frame C)))) : v = w := by
  rcases le_total t t' with hle | hle
  · exact halted_le h hle ht ht'
  · exact (halted_le h hle ht' ht).symm

/-- **Correctness of the evaluator.**  The machine reaches the halted state
`(ret true, [])` if and only if `reach R K a b` holds. -/
theorem interp_accepts_iff (h : IsInterp K R dstep) (a b : C) :
    Reaches dstep (Mode.ask a b, ([] : List (Frame C))) (Mode.ret true, []) ↔
      reach R K a b = true := by
  have hrun : Reaches dstep (Mode.ask a b, ([] : List (Frame C)))
      (Mode.ret (reach R K a b), []) := askEval h K [] (by simp) a b
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := hrun
    exact (halted_unique h ht ht').symm
  · intro hb
    rw [hb] at hrun
    exact hrun

end Interp

end CS

/-
Space-bounded computation: the model.

A *device* is a configuration graph with read-only access to the input word.
Concretely, a device has

* a type `Conf` of configurations,
* a function `head : Conf → ℕ` giving the position of the input head in each
  configuration,
* a transition relation (resp. function) which, given the current configuration
  and the symbol currently scanned on the input tape, describes the possible
  (resp. the unique) successor configuration,
* an initial configuration and a set of accepting configurations.

The *space* used by such a device is the number of bits needed to write down a
configuration, i.e. `s` such that `Conf` embeds into `Fin s → Bool`.  This is the
standard abstract way of measuring space: a Turing machine with a read-only
input tape and a work tape of `s` cells over a fixed finite work alphabet has
`2^{O(s)}` configurations (plus the input head position, recorded here by
`head`), and conversely.

`NSPACE f` (resp. `DSPACE f`) is the class of languages decided by a family of
nondeterministic (resp. deterministic) devices, one for each input length, whose
configuration space uses at most `f n` bits.

Two remarks on the formalisation.

* A member of a space class is a *family* of devices indexed by the input length,
  with no uniformity condition relating the different lengths; this is the
  non-uniform reading of a space class.  Savitch's construction below is
  nevertheless uniform in the device: the deterministic device is obtained from
  the nondeterministic one by one explicit transformation, applied length by
  length.
* Space is counted in bits, so `f n = 0` allows a single configuration only.
  Accordingly the deterministic bound obtained below is `16 * (f n + 1) ^ 2`,
  which is `O(f²)` and also meaningful when `f n = 0`.
-/
import Mathlib

namespace CS

/-- A language over the alphabet `Γ`. -/
abbrev Language (Γ : Type) := List Γ → Prop

/-- A nondeterministic space-bounded device (a configuration graph together with
read-only access to the input). -/
structure NDevice (Γ : Type) where
  /-- The type of configurations. -/
  Conf : Type
  /-- Position of the input head in a configuration. -/
  head : Conf → ℕ
  /-- `step c σ c'` holds if `c'` is a possible successor of `c` when the symbol
  scanned on the input tape is `σ` (`none` meaning "past the end of the input"). -/
  step : Conf → Option Γ → Conf → Prop
  /-- The initial configuration. -/
  init : Conf
  /-- The accepting configurations. -/
  acc : Conf → Prop

/-- A deterministic space-bounded device. -/
structure DDevice (Γ : Type) where
  /-- The type of configurations. -/
  Conf : Type
  /-- Position of the input head in a configuration. -/
  head : Conf → ℕ
  /-- The successor of a configuration, given the scanned input symbol. -/
  step : Conf → Option Γ → Conf
  /-- The initial configuration. -/
  init : Conf
  /-- The accepting configurations. -/
  acc : Conf → Prop

namespace NDevice

variable {Γ : Type}

/-- A device runs in space `s` if its configurations can be encoded by `s` bits. -/
def SpaceBound (M : NDevice Γ) (s : ℕ) : Prop :=
  ∃ e : M.Conf → (Fin s → Bool), Function.Injective e

/-- The one-step relation on configurations induced by a concrete input `x`. -/
def stepOn (M : NDevice Γ) (x : List Γ) (a b : M.Conf) : Prop :=
  M.step a x[M.head a]? b

/-- A nondeterministic device accepts `x` if some accepting configuration is
reachable from the initial one. -/
def Accepts (M : NDevice Γ) (x : List Γ) : Prop :=
  ∃ c, Relation.ReflTransGen (M.stepOn x) M.init c ∧ M.acc c

end NDevice

namespace DDevice

variable {Γ : Type}

/-- A device runs in space `s` if its configurations can be encoded by `s` bits. -/
def SpaceBound (M : DDevice Γ) (s : ℕ) : Prop :=
  ∃ e : M.Conf → (Fin s → Bool), Function.Injective e

/-- The configuration of `M` on input `x` after `t` steps. -/
def run (M : DDevice Γ) (x : List Γ) : ℕ → M.Conf
  | 0 => M.init
  | t + 1 => M.step (M.run x t) x[M.head (M.run x t)]?

/-- A deterministic device accepts `x` if its (unique) run reaches an accepting
configuration. -/
def Accepts (M : DDevice Γ) (x : List Γ) : Prop :=
  ∃ t, M.acc (M.run x t)

end DDevice

/-- `NSPACE f` : languages decided by nondeterministic devices using `f n` bits of
space on inputs of length `n`. -/
def NSPACE (Γ : Type) (f : ℕ → ℕ) : Set (Language Γ) :=
  {L | ∃ M : ℕ → NDevice Γ, (∀ n, (M n).SpaceBound (f n)) ∧
        ∀ x : List Γ, (L x ↔ (M x.length).Accepts x)}

/-- `DSPACE f` : languages decided by deterministic devices using `f n` bits of
space on inputs of length `n`. -/
def DSPACE (Γ : Type) (f : ℕ → ℕ) : Set (Language Γ) :=
  {L | ∃ M : ℕ → DDevice Γ, (∀ n, (M n).SpaceBound (f n)) ∧
        ∀ x : List Γ, (L x ↔ (M x.length).Accepts x)}

end CS

/-
Reachability in a finite graph, and Savitch's midpoint recursion.

For a relation `R` on a finite type `C` we define

  `reach R 0 a b        ↔ a = b ∨ R a b`
  `reach R (k+1) a b    ↔ ∃ m, reach R k a m ∧ reach R k m b`

so that `reach R k a b` says exactly that `b` is reachable from `a` by at most
`2 ^ k` steps.  The main result of this file, `reach_iff`, states that as soon as
`2 ^ k` is at least the number of vertices, `reach R k` is precisely the
reflexive-transitive closure of `R`.  This is the combinatorial heart of
Savitch's theorem: the recursion has depth `k ≈ log |C|` and each level only has
to remember one vertex.
-/
import Mathlib

namespace CS

/-- Classical decision of a proposition as a boolean. -/
noncomputable def bdec (p : Prop) : Bool := @decide p (Classical.dec p)

@[simp] lemma bdec_eq_true_iff {p : Prop} : bdec p = true ↔ p := by
  unfold bdec; simp

lemma bdec_eq_false_iff {p : Prop} : bdec p = false ↔ ¬ p := by
  rw [← Bool.not_eq_true, bdec_eq_true_iff]

lemma bdec_of {p : Prop} (hp : p) : bdec p = true := bdec_eq_true_iff.2 hp

section

variable {C : Type} (R : C → C → Prop)

/-- `Walk R v ℓ a b` : the function `v` traces a walk of length `ℓ` from `a` to
`b` in the graph `R`. -/
def Walk (v : ℕ → C) (ℓ : ℕ) (a b : C) : Prop :=
  v 0 = a ∧ v ℓ = b ∧ ∀ i < ℓ, R (v i) (v (i + 1))

/-- Savitch's midpoint recursion: `reach R k a b` holds iff `b` can be reached
from `a` in at most `2 ^ k` steps. -/
noncomputable def reach : ℕ → C → C → Bool
  | 0, a, b => bdec (a = b ∨ R a b)
  | k + 1, a, b => bdec (∃ m : C, reach k a m = true ∧ reach k m b = true)

@[simp] lemma reach_zero (a b : C) : reach R 0 a b = bdec (a = b ∨ R a b) := rfl

@[simp] lemma reach_succ (k : ℕ) (a b : C) :
    reach R (k + 1) a b = bdec (∃ m : C, reach R k a m = true ∧ reach R k m b = true) := rfl

variable {R}

lemma reach_refl (k : ℕ) (a : C) : reach R k a a = true := by
  induction k with
  | zero => simp
  | succ k ih => simp only [reach_succ, bdec_eq_true_iff]; exact ⟨a, ih, ih⟩

lemma reach_succ_of_reach {k : ℕ} {a b : C} (h : reach R k a b = true) :
    reach R (k + 1) a b = true := by
  simp only [reach_succ, bdec_eq_true_iff]
  exact ⟨b, h, reach_refl k b⟩

/-- Soundness of the recursion. -/
lemma reflTransGen_of_reach : ∀ (k : ℕ) {a b : C}, reach R k a b = true →
    Relation.ReflTransGen R a b := by
  intro k
  induction k with
  | zero =>
      intro a b h
      simp only [reach_zero, bdec_eq_true_iff] at h
      rcases h with h | h
      · exact h ▸ Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single h
  | succ k ih =>
      intro a b h
      simp only [reach_succ, bdec_eq_true_iff] at h
      obtain ⟨m, h1, h2⟩ := h
      exact (ih h1).trans (ih h2)

/-- A walk of length at most `2 ^ k` is found by the recursion. -/
lemma reach_of_walk : ∀ (k : ℕ) {v : ℕ → C} {ℓ : ℕ} {a b : C},
    Walk R v ℓ a b → ℓ ≤ 2 ^ k → reach R k a b = true := by
  intro k
  induction k with
  | zero =>
      rintro v ℓ a b ⟨h0, hl, hstep⟩ hle
      simp only [pow_zero] at hle
      interval_cases ℓ
      · exact bdec_of (Or.inl (by rw [← h0, ← hl]))
      · have := hstep 0 (by norm_num)
        rw [h0] at this
        rw [show (0 : ℕ) + 1 = 1 from rfl] at this
        exact bdec_of (Or.inr (by rw [← hl]; exact this))
  | succ k ih =>
      rintro v ℓ a b ⟨h0, hl, hstep⟩ hle
      set i := min ℓ (2 ^ k) with hi
      have hile : i ≤ ℓ := min_le_left _ _
      have hi1 : i ≤ 2 ^ k := min_le_right _ _
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      have hi2 : ℓ - i ≤ 2 ^ k := by omega
      have w1 : Walk R v i a (v i) := ⟨h0, rfl, fun j hj => hstep j (lt_of_lt_of_le hj hile)⟩
      have w2 : Walk R (fun t => v (i + t)) (ℓ - i) (v i) b :=
        ⟨by simp, by simp only []; rw [Nat.add_sub_cancel' hile]; exact hl,
         fun j hj => by
           have : i + j < ℓ := by omega
           simpa [Nat.add_assoc] using hstep (i + j) this⟩
      simp only [reach_succ, bdec_eq_true_iff]
      exact ⟨v i, ih w1 hi1, ih w2 hi2⟩

lemma reflTransGen_of_walk : ∀ {ℓ : ℕ} {v : ℕ → C} {a b : C}, Walk R v ℓ a b →
    Relation.ReflTransGen R a b := by
  intro ℓ
  induction ℓ with
  | zero =>
      rintro v a b ⟨h0, hl, _⟩
      exact h0 ▸ hl ▸ Relation.ReflTransGen.refl
  | succ ℓ ih =>
      rintro v a b ⟨h0, hl, hstep⟩
      have w : Walk R v ℓ a (v ℓ) := ⟨h0, rfl, fun j hj => hstep j (by omega)⟩
      exact (ih w).tail (hl ▸ hstep ℓ (by omega))

lemma walk_of_reflTransGen {a b : C} (h : Relation.ReflTransGen R a b) :
    ∃ v ℓ, Walk R v ℓ a b := by
  induction h with
  | refl => exact ⟨fun _ => a, 0, rfl, rfl, by omega⟩
  | tail hab hbc ih =>
      obtain ⟨v, ℓ, h0, hl, hstep⟩ := ih
      rename_i b' c'
      refine ⟨fun t => if t ≤ ℓ then v t else c', ℓ + 1, ?_, ?_, ?_⟩
      · simpa using h0
      · simp
      · intro j hj
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
        · have h1 : j ≤ ℓ := h.le
          have h2 : j + 1 ≤ ℓ := h
          simp only [if_pos h1, if_pos h2]
          exact hstep j h
        · subst h
          simp only [if_pos (le_refl j), if_neg (by omega : ¬ j + 1 ≤ j)]
          exact hl ▸ hbc

/-- Cutting a loop out of a walk. -/
lemma walk_splice {v : ℕ → C} {ℓ i j : ℕ} {a b : C} (hw : Walk R v ℓ a b)
    (hij : i < j) (hj : j ≤ ℓ) (heq : v i = v j) :
    Walk R (fun t => if t ≤ i then v t else v (t + (j - i))) (ℓ - (j - i)) a b := by
  obtain ⟨h0, hl, hstep⟩ := hw
  set d := j - i with hd
  have hd0 : 0 < d := by omega
  refine ⟨by simpa using h0, ?_, ?_⟩
  · by_cases h : ℓ - d ≤ i
    · have hjl : j = ℓ := by omega
      have hli : ℓ - d = i := by omega
      simp only [if_pos h]
      rw [hli, heq, hjl]
      exact hl
    · simp only [if_neg h, show ℓ - d + d = ℓ by omega]
      exact hl
  · intro t ht
    rcases lt_trichotomy t i with h | h | h
    · have h1 : t ≤ i := h.le
      have h2 : t + 1 ≤ i := h
      simp only [if_pos h1, if_pos h2]
      exact hstep t (by omega)
    · subst h
      simp only [if_pos (le_refl t), if_neg (by omega : ¬ t + 1 ≤ t)]
      rw [heq, show t + 1 + d = j + 1 by omega]
      exact hstep j (by omega)
    · simp only [if_neg (by omega : ¬ t ≤ i), if_neg (by omega : ¬ t + 1 ≤ i)]
      rw [show t + 1 + d = (t + d) + 1 by omega]
      exact hstep (t + d) (by omega)

variable [Fintype C]

/-- In a finite graph, any walk can be shortened to one of length less than the
number of vertices. -/
lemma walk_short : ∀ (ℓ : ℕ) {v : ℕ → C} {a b : C}, Walk R v ℓ a b →
    ∃ v' ℓ', ℓ' < Fintype.card C ∧ Walk R v' ℓ' a b := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro v a b hw
    by_cases hlt : ℓ < Fintype.card C
    · exact ⟨v, ℓ, hlt, hw⟩
    · push_neg at hlt
      have hcard : Fintype.card C < Fintype.card (Fin (ℓ + 1)) := by
        simpa using Nat.lt_succ_of_le hlt
      obtain ⟨p, q, hpq, hval⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt (fun t : Fin (ℓ + 1) => v t) hcard
      have hne : (p : ℕ) ≠ (q : ℕ) := fun h => hpq (Fin.ext h)
      rcases lt_or_gt_of_ne hne with h | h
      · have hq : (q : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp q.isLt
        have := walk_splice hw h hq hval
        exact ih _ (by omega) this
      · have hp : (p : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp p.isLt
        have := walk_splice hw h hp hval.symm
        exact ih _ (by omega) this

/-- **Savitch's recursion is correct**: if `2 ^ k` is at least the number of
vertices, `reach R k` is reachability. -/
theorem reach_iff {k : ℕ} (hcard : Fintype.card C ≤ 2 ^ k) (a b : C) :
    reach R k a b = true ↔ Relation.ReflTransGen R a b := by
  constructor
  · exact reflTransGen_of_reach k
  · intro h
    obtain ⟨v, ℓ, hw⟩ := walk_of_reflTransGen h
    obtain ⟨v', ℓ', hlt, hw'⟩ := walk_short ℓ hw
    exact reach_of_walk k hw' (by omega)

end

end CS

