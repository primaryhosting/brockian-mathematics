/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The isolation engine's model

A proof-carrying app is modelled as a small nondeterministic program `Prog`.
Running it emits *effects*: either the exercise of a capability (`Effect.cap`)
or the touching of a memory address (`Effect.mem`).

A `Sandbox` fixes which capabilities are granted and how large the isolated
memory region is.  An app *escapes* the sandbox if some reachable configuration
of its small-step operational semantics emits an effect the sandbox does not
permit.

The engine certifies apps in two independent ways:

* a **static capability scan** (`Clean`), a decidable syntactic check, and
* a **memory-safety certificate** (`Proved`), an inductive derivation shipped
  with the app.

The target theorem `no_clean_proved_with_escape` is the *soundness* of this
certification: no app can be clean, proved and still escape.  The converse,
`clean_and_proved_of_not_escapes`, is its *completeness*: every non-escaping
app is accepted by both certificates.  Both certificates are load-bearing and
the statement is non-vacuous; see the examples at the end of the file.

The development is self-contained (no imports), so that the file can begin with
the required header comment.
-/

namespace PCA
namespace Isolation

/-- Capabilities that an app may exercise. -/
inductive Cap
  | read
  | write
  | net
  | exec
  | spawnProc
  deriving DecidableEq, Repr

/-- Memory addresses. -/
abbrev Addr := Nat

/-- Observable effects of a single execution step. -/
inductive Effect
  | cap (c : Cap)
  | mem (a : Addr)
  deriving DecidableEq, Repr

/-- A sandbox: the granted capabilities and the size of the isolated region. -/
structure Sandbox where
  /-- Which capabilities the sandbox grants. -/
  allowed : Cap → Bool
  /-- The size of the isolated memory region: addresses `< size` are internal. -/
  size : Nat

/-- The effects a sandbox permits. -/
def Sandbox.Permits (s : Sandbox) : Effect → Prop
  | .cap c => s.allowed c = true
  | .mem a => a < s.size

instance (s : Sandbox) : (e : Effect) → Decidable (s.Permits e)
  | .cap c => inferInstanceAs (Decidable (s.allowed c = true))
  | .mem a => inferInstanceAs (Decidable (a < s.size))

/-- Apps: straight-line code with capability uses, memory touches,
nondeterministic branching and loops. -/
inductive Prog
  | skip
  | use (c : Cap) (k : Prog)
  | touch (a : Addr) (k : Prog)
  | branch (t e : Prog)
  | loop (body : Prog) (k : Prog)
  deriving Repr

/-- Sequential composition: run `p`, then continue with `q`. -/
def Prog.append : Prog → Prog → Prog
  | .skip, q => q
  | .use c k, q => .use c (k.append q)
  | .touch a k, q => .touch a (k.append q)
  | .branch t e, q => .branch (t.append q) (e.append q)
  | .loop b k, q => .loop b (k.append q)

/-- `effects p e` holds when the effect `e` occurs syntactically in `p`. -/
def effects : Prog → Effect → Prop
  | .skip, _ => False
  | .use c k, e => e = Effect.cap c ∨ effects k e
  | .touch a k, e => e = Effect.mem a ∨ effects k e
  | .branch t e', e => effects t e ∨ effects e' e
  | .loop b k, e => effects b e ∨ effects k e

/-- Small-step operational semantics, labelled by the emitted effect. -/
inductive Step : Prog → Option Effect → Prog → Prop
  | use (c k) : Step (.use c k) (some (.cap c)) k
  | touch (a k) : Step (.touch a k) (some (.mem a)) k
  | branchL (t e) : Step (.branch t e) none t
  | branchR (t e) : Step (.branch t e) none e
  | loopIter (b k) : Step (.loop b k) none (b.append (.loop b k))
  | loopExit (b k) : Step (.loop b k) none k

/-- Reachability in the operational semantics (labels forgotten). -/
inductive Steps : Prog → Prog → Prop
  | refl (p) : Steps p p
  | head {p q r : Prog} {o : Option Effect} : Step p o q → Steps q r → Steps p r

/-- `Emits p e` : some configuration reachable from `p` emits the effect `e`. -/
def Emits (p : Prog) (e : Effect) : Prop :=
  ∃ q r, Steps p q ∧ Step q (some e) r

/-- The app escapes the sandbox: it can emit an effect the sandbox forbids. -/
def Escapes (s : Sandbox) (p : Prog) : Prop :=
  ∃ e, Emits p e ∧ ¬ s.Permits e

/-- The engine's decidable capability scanner. -/
def scan (s : Sandbox) : Prog → Bool
  | .skip => true
  | .use c k => s.allowed c && scan s k
  | .touch _ k => scan s k
  | .branch t e => scan s t && scan s e
  | .loop b k => scan s b && scan s k

/-- An app is *clean* when the engine's capability scanner accepts it. -/
def Clean (s : Sandbox) (p : Prog) : Prop := scan s p = true

instance (s : Sandbox) (p : Prog) : Decidable (Clean s p) :=
  inferInstanceAs (Decidable (scan s p = true))

/-- The memory-safety certificate carried by a proof-carrying app. -/
inductive MemSafe (s : Sandbox) : Prog → Prop
  | skip : MemSafe s .skip
  | use (c k) : MemSafe s k → MemSafe s (.use c k)
  | touch (a k) : a < s.size → MemSafe s k → MemSafe s (.touch a k)
  | branch (t e) : MemSafe s t → MemSafe s e → MemSafe s (.branch t e)
  | loop (b k) : MemSafe s b → MemSafe s k → MemSafe s (.loop b k)

/-- An app is *proved* when it carries a memory-safety certificate. -/
def Proved (s : Sandbox) (p : Prog) : Prop := MemSafe s p

/-! ## Effects and sequential composition -/

@[simp] theorem effects_skip (e : Effect) : effects .skip e ↔ False := Iff.rfl

@[simp] theorem effects_use (c : Cap) (k : Prog) (e : Effect) :
    effects (.use c k) e ↔ e = Effect.cap c ∨ effects k e := Iff.rfl

@[simp] theorem effects_touch (a : Addr) (k : Prog) (e : Effect) :
    effects (.touch a k) e ↔ e = Effect.mem a ∨ effects k e := Iff.rfl

@[simp] theorem effects_branch (t e' : Prog) (e : Effect) :
    effects (.branch t e') e ↔ effects t e ∨ effects e' e := Iff.rfl

@[simp] theorem effects_loop (b k : Prog) (e : Effect) :
    effects (.loop b k) e ↔ effects b e ∨ effects k e := Iff.rfl

@[simp] theorem Prog.append_skip (p : Prog) : p.append .skip = p := by
  induction p <;> simp [Prog.append, *]

theorem effects_append (p q : Prog) (e : Effect) :
    effects (p.append q) e ↔ effects p e ∨ effects q e := by
  induction p generalizing q with
  | skip => simp [Prog.append]
  | use c k ih => simp [Prog.append, ih, or_assoc]
  | touch a k ih => simp [Prog.append, ih, or_assoc]
  | branch t e' iht ihe =>
      simp only [Prog.append, effects_branch, iht, ihe]
      constructor
      · rintro ((h | h) | (h | h))
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inr h)
  | loop b k _ ihk => simp [Prog.append, ihk, or_assoc]

/-! ## The syntactic effect set is exactly the set of reachable effects -/

theorem effects_of_step {p q : Prog} {o : Option Effect} (h : Step p o q) :
    ∀ e, effects q e → effects p e := by
  cases h with
  | use c k => intro e he; exact Or.inr he
  | touch a k => intro e he; exact Or.inr he
  | branchL t e' => intro e he; exact Or.inl he
  | branchR t e' => intro e he; exact Or.inr he
  | loopIter b k =>
      intro e he
      rcases (effects_append b (.loop b k) e).1 he with h | h
      · exact Or.inl h
      · exact h
  | loopExit b k => intro e he; exact Or.inr he

theorem effects_of_steps {p q : Prog} (h : Steps p q) :
    ∀ e, effects q e → effects p e := by
  induction h with
  | refl p => exact fun _ he => he
  | head hstep _ ih => exact fun e he => effects_of_step hstep e (ih e he)

theorem effects_of_emitting_step {p q : Prog} {e : Effect}
    (h : Step p (some e) q) : effects p e := by
  cases h with
  | use c k => exact Or.inl rfl
  | touch a k => exact Or.inl rfl

/-- **Soundness of the static effect analysis**: every effect emitted at
runtime occurs syntactically in the app. -/
theorem effects_of_emits {p : Prog} {e : Effect} (h : Emits p e) :
    effects p e := by
  obtain ⟨q, r, hsteps, hstep⟩ := h
  exact effects_of_steps hsteps e (effects_of_emitting_step hstep)

theorem Emits.of_step {p p' : Prog} {o : Option Effect} {e : Effect}
    (h : Step p o p') (h' : Emits p' e) : Emits p e := by
  obtain ⟨q, r, hsteps, hstep⟩ := h'
  exact ⟨q, r, Steps.head h hsteps, hstep⟩

theorem emits_append_of_effects (e : Effect) :
    ∀ (p q : Prog), effects p e → Emits (p.append q) e := by
  intro p
  induction p with
  | skip => intro q h; exact h.elim
  | use c k ih =>
      intro q h
      rcases h with h | h
      · subst h
        exact ⟨_, _, Steps.refl _, Step.use c (k.append q)⟩
      · exact Emits.of_step (Step.use c (k.append q)) (ih q h)
  | touch a k ih =>
      intro q h
      rcases h with h | h
      · subst h
        exact ⟨_, _, Steps.refl _, Step.touch a (k.append q)⟩
      · exact Emits.of_step (Step.touch a (k.append q)) (ih q h)
  | branch t e' iht ihe =>
      intro q h
      rcases h with h | h
      · exact Emits.of_step (Step.branchL (t.append q) (e'.append q)) (iht q h)
      · exact Emits.of_step (Step.branchR (t.append q) (e'.append q)) (ihe q h)
  | loop b k ihb ihk =>
      intro q h
      rcases h with h | h
      · exact Emits.of_step (Step.loopIter b (k.append q))
          (ihb (.loop b (k.append q)) h)
      · exact Emits.of_step (Step.loopExit b (k.append q)) (ihk q h)

/-- **Completeness of the static effect analysis**: every syntactically
occurring effect really is emitted by some run. -/
theorem emits_of_effects {p : Prog} {e : Effect} (h : effects p e) :
    Emits p e := by
  have := emits_append_of_effects e p .skip h
  simpa using this

/-- The static effect analysis computes exactly the reachable effects. -/
theorem emits_iff_effects (p : Prog) (e : Effect) :
    Emits p e ↔ effects p e :=
  ⟨effects_of_emits, emits_of_effects⟩

/-- Escape, reformulated syntactically. -/
theorem escapes_iff (s : Sandbox) (p : Prog) :
    Escapes s p ↔ ∃ e, effects p e ∧ ¬ s.Permits e := by
  constructor
  · rintro ⟨e, he, hne⟩; exact ⟨e, effects_of_emits he, hne⟩
  · rintro ⟨e, he, hne⟩; exact ⟨e, emits_of_effects he, hne⟩

/-! ## Correctness of the two certificates -/

/-- The capability scanner accepts exactly the apps all of whose capability
uses are granted. -/
theorem clean_iff (s : Sandbox) (p : Prog) :
    Clean s p ↔ ∀ c : Cap, effects p (Effect.cap c) → s.allowed c = true := by
  unfold Clean
  induction p with
  | skip => simp [scan]
  | use c k ih =>
      simp only [scan, Bool.and_eq_true, ih, effects_use]
      constructor
      · rintro ⟨hc, hk⟩ c' hc'
        rcases hc' with h | h
        · cases h; exact hc
        · exact hk c' h
      · intro h
        exact ⟨h c (Or.inl rfl), fun c' hc' => h c' (Or.inr hc')⟩
  | touch a k ih => simpa [scan] using ih
  | branch t e iht ihe =>
      simp only [scan, Bool.and_eq_true, iht, ihe, effects_branch]
      constructor
      · rintro ⟨h1, h2⟩ c hc; rcases hc with h | h
        · exact h1 c h
        · exact h2 c h
      · intro h
        exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  | loop b k ihb ihk =>
      simp only [scan, Bool.and_eq_true, ihb, ihk, effects_loop]
      constructor
      · rintro ⟨h1, h2⟩ c hc; rcases hc with h | h
        · exact h1 c h
        · exact h2 c h
      · intro h
        exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩

/-- A memory-safety certificate exists exactly when every touched address lies
inside the isolated region. -/
theorem proved_iff (s : Sandbox) (p : Prog) :
    Proved s p ↔ ∀ a : Addr, effects p (Effect.mem a) → a < s.size := by
  unfold Proved
  constructor
  · intro h
    induction h with
    | skip => intro a ha; exact ha.elim
    | use c k _ ih =>
        intro a ha
        rcases ha with h | h
        · exact absurd h (by simp)
        · exact ih a h
    | touch a k hlt _ ih =>
        intro b hb
        rcases hb with h | h
        · cases h; exact hlt
        · exact ih b h
    | branch t e _ _ iht ihe =>
        intro a ha; rcases ha with h | h
        · exact iht a h
        · exact ihe a h
    | loop b k _ _ ihb ihk =>
        intro a ha; rcases ha with h | h
        · exact ihb a h
        · exact ihk a h
  · intro h
    induction p with
    | skip => exact MemSafe.skip
    | use c k ih => exact MemSafe.use c k (ih fun a ha => h a (Or.inr ha))
    | touch a k ih =>
        exact MemSafe.touch a k (h a (Or.inl rfl))
          (ih fun b hb => h b (Or.inr hb))
    | branch t e iht ihe =>
        exact MemSafe.branch t e (iht fun a ha => h a (Or.inl ha))
          (ihe fun a ha => h a (Or.inr ha))
    | loop b k ihb ihk =>
        exact MemSafe.loop b k (ihb fun a ha => h a (Or.inl ha))
          (ihk fun a ha => h a (Or.inr ha))

/-! ## Main results -/

/-- **Soundness of the isolation engine.**  No app is simultaneously clean
(accepted by the capability scanner), proved (carrying a memory-safety
certificate) and able to escape its sandbox. -/
theorem no_clean_proved_with_escape (s : Sandbox) (p : Prog) :
    ¬ (Clean s p ∧ Proved s p ∧ Escapes s p) := by
  rintro ⟨hclean, hproved, hesc⟩
  obtain ⟨e, heff, hne⟩ := (escapes_iff s p).1 hesc
  cases e with
  | cap c => exact hne ((clean_iff s p).1 hclean c heff)
  | mem a => exact hne ((proved_iff s p).1 hproved a heff)

/-- **Completeness of the isolation engine.**  Every app that cannot escape is
accepted by both certificates. -/
theorem clean_and_proved_of_not_escapes (s : Sandbox) (p : Prog)
    (h : ¬ Escapes s p) : Clean s p ∧ Proved s p := by
  rw [escapes_iff] at h
  have h' : ∀ e, effects p e → s.Permits e := by
    intro e he
    by_cases hp : s.Permits e
    · exact hp
    · exact absurd ⟨e, he, hp⟩ h
  exact ⟨(clean_iff s p).2 fun c hc => h' _ hc,
    (proved_iff s p).2 fun a ha => h' _ ha⟩

/-- The engine's certification is exact: an app is clean and proved iff it
cannot escape its sandbox. -/
theorem clean_and_proved_iff_not_escapes (s : Sandbox) (p : Prog) :
    (Clean s p ∧ Proved s p) ↔ ¬ Escapes s p :=
  ⟨fun h hesc => no_clean_proved_with_escape s p ⟨h.1, h.2, hesc⟩,
    clean_and_proved_of_not_escapes s p⟩

/-! ## Non-vacuity

Both certificates are load-bearing: dropping either one admits an escaping app.
We also exhibit an app that is accepted by both, so the soundness theorem is
not vacuous.
-/

/-- A sandbox granting only `read`, with a two-cell memory region. -/
def demoBox : Sandbox := ⟨fun c => decide (c = Cap.read), 2⟩

/-- A well-behaved app: reads and touches an in-bounds cell, inside a loop. -/
def goodApp : Prog := .loop (.use .read (.touch 1 .skip)) .skip

theorem goodApp_proved : Proved demoBox goodApp := by
  rw [proved_iff]
  intro a ha
  simp [goodApp] at ha
  subst ha
  decide

theorem goodApp_clean : Clean demoBox goodApp := by decide

/-- The good app is accepted, hence provably confined. -/
theorem goodApp_not_escapes : ¬ Escapes demoBox goodApp :=
  (clean_and_proved_iff_not_escapes demoBox goodApp).1 ⟨goodApp_clean, goodApp_proved⟩

/-- An app that opens a network socket: memory-safe, but not clean. -/
def netApp : Prog := .use .net .skip

theorem netApp_proved_not_clean_escapes :
    Proved demoBox netApp ∧ ¬ Clean demoBox netApp ∧ Escapes demoBox netApp := by
  refine ⟨?_, by decide, ?_⟩
  · rw [proved_iff]; intro a ha; simp [netApp] at ha
  · rw [escapes_iff]
    exact ⟨Effect.cap .net, Or.inl rfl, by decide⟩

/-- An app that touches memory outside the region: clean, but not memory-safe. -/
def oobApp : Prog := .touch 7 .skip

theorem oobApp_clean_not_proved_escapes :
    Clean demoBox oobApp ∧ ¬ Proved demoBox oobApp ∧ Escapes demoBox oobApp := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [proved_iff]
    intro h
    have := h 7 (Or.inl rfl)
    simp [demoBox] at this
  · rw [escapes_iff]
    exact ⟨Effect.mem 7, Or.inl rfl, by decide⟩

end Isolation
end PCA

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

