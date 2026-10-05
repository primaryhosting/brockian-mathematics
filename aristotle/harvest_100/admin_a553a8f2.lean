/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This module formalises the model of a capability-based *isolation engine* for
proof-carrying applications, together with its soundness **and** completeness.

* A region (`Region`) is an abstract resource name; a capability set (`CapSet`)
  is a decidable set of regions, represented by its characteristic function.
* An application's code is a program (`Prog`) of a small nondeterministic
  language with capability acquisition/release and resource accesses.
* `Exec` is the operational semantics of the isolation engine at run time: a
  resource access only produces an observable effect when the corresponding
  capability is currently held; otherwise the engine *denies* it silently.
* `App.Escapes` says that some run of the application observably touches a
  resource outside its policy (its sandbox boundary).
* `Cert` is the proof system for capability certificates that a proof-carrying
  app ships with its code, and `check` is the engine's decidable checker.

The main results are:

* `cert_sound`  : a valid certificate forbids any escape;
* `check_cert`  : the checker synthesises a certificate (so `Clean → Proved`);
* `check_complete` : if the checker rejects, an escaping run really exists;
* `no_clean_proved_with_escape` : the target theorem;
* `clean_proved_iff_no_escape` : soundness *and* completeness of the engine.

The development is deliberately self-contained (no imports), so that the header
comment above is literally the first thing in the file.
-/

namespace PCA.Isolation

/-! ## Capability sets -/

/-- Abstract resource names. -/
abbrev Region := Nat

/-- A capability set, represented by its characteristic function. -/
abbrev CapSet := Region → Bool

/-- Add a capability. -/
def insertCap (r : Region) (H : CapSet) : CapSet := fun x => (x == r) || H x

/-- Drop a capability. -/
def eraseCap (r : Region) (H : CapSet) : CapSet := fun x => (!(x == r)) && H x

/-- Union of capability sets. -/
def unionCap (H₁ H₂ : CapSet) : CapSet := fun x => H₁ x || H₂ x

/-- Containment of capability sets. -/
def CapSub (A B : CapSet) : Prop := ∀ x, A x = true → B x = true

theorem CapSub.refl (A : CapSet) : CapSub A A := fun _ h => h

theorem mem_insertCap {r x : Region} {H : CapSet} :
    insertCap r H x = true ↔ x = r ∨ H x = true := by
  simp [insertCap]

theorem mem_eraseCap {r x : Region} {H : CapSet} :
    eraseCap r H x = true ↔ x ≠ r ∧ H x = true := by
  simp [eraseCap]

theorem mem_unionCap {x : Region} {H₁ H₂ : CapSet} :
    unionCap H₁ H₂ x = true ↔ H₁ x = true ∨ H₂ x = true := by
  simp [unionCap]

theorem insertCap_mono {A B : CapSet} (h : CapSub A B) (r : Region) :
    CapSub (insertCap r A) (insertCap r B) := by
  intro x hx
  rcases mem_insertCap.mp hx with hx | hx
  · exact mem_insertCap.mpr (Or.inl hx)
  · exact mem_insertCap.mpr (Or.inr (h x hx))

theorem eraseCap_mono {A B : CapSet} (h : CapSub A B) (r : Region) :
    CapSub (eraseCap r A) (eraseCap r B) := by
  intro x hx
  rcases mem_eraseCap.mp hx with ⟨h1, h2⟩
  exact mem_eraseCap.mpr ⟨h1, h x h2⟩

/-! ## Programs -/

/-- The application language of the isolation engine. -/
inductive Prog where
  /-- Do nothing. -/
  | nop : Prog
  /-- Ask the capability manager for a handle on region `r`. -/
  | acquire (r : Region) : Prog
  /-- Give back the handle on region `r`. -/
  | release (r : Region) : Prog
  /-- Try to touch region `r`. -/
  | access (r : Region) : Prog
  /-- Sequential composition. -/
  | seq (p q : Prog) : Prog
  /-- Nondeterministic choice (e.g. a data-dependent branch). -/
  | choice (p q : Prog) : Prog
  deriving DecidableEq, Repr

/-! ## Operational semantics of the isolation engine

`Exec p h h' t` : running `p` with capabilities `h` may terminate with
capabilities `h'`, observably touching exactly the regions listed in `t`.
The engine mediates every access: an access to a region whose capability is not
held is denied and leaves no observable effect. -/
inductive Exec : Prog → CapSet → CapSet → List Region → Prop where
  | nop (h : CapSet) : Exec .nop h h []
  | acquire (r : Region) (h : CapSet) : Exec (.acquire r) h (insertCap r h) []
  | release (r : Region) (h : CapSet) : Exec (.release r) h (eraseCap r h) []
  | accessOk (r : Region) (h : CapSet) (hr : h r = true) : Exec (.access r) h h [r]
  | accessDenied (r : Region) (h : CapSet) (hr : h r = false) : Exec (.access r) h h []
  | seq {p q : Prog} {h h₁ h₂ : CapSet} {t₁ t₂ : List Region} :
      Exec p h h₁ t₁ → Exec q h₁ h₂ t₂ → Exec (.seq p q) h h₂ (t₁ ++ t₂)
  | choiceL {p q : Prog} {h h' : CapSet} {t : List Region} :
      Exec p h h' t → Exec (.choice p q) h h' t
  | choiceR {p q : Prog} {h h' : CapSet} {t : List Region} :
      Exec q h h' t → Exec (.choice p q) h h' t

/-- The engine never gets stuck: every program has at least one run. -/
theorem exec_progress (p : Prog) (h : CapSet) : ∃ h' t, Exec p h h' t := by
  induction p generalizing h with
  | nop => exact ⟨h, [], .nop h⟩
  | acquire r => exact ⟨insertCap r h, [], .acquire r h⟩
  | release r => exact ⟨eraseCap r h, [], .release r h⟩
  | access r =>
      cases hr : h r with
      | false => exact ⟨h, [], .accessDenied r h hr⟩
      | true => exact ⟨h, [r], .accessOk r h hr⟩
  | seq p q ihp ihq =>
      obtain ⟨h₁, t₁, e₁⟩ := ihp h
      obtain ⟨h₂, t₂, e₂⟩ := ihq h₁
      exact ⟨h₂, t₁ ++ t₂, .seq e₁ e₂⟩
  | choice p q ihp _ =>
      obtain ⟨h', t, e⟩ := ihp h
      exact ⟨h', t, .choiceL e⟩

/-! ## Escapes -/

/-- A trace escapes the policy `P` if it observably touches a region outside `P`. -/
def EscapingTrace (P : CapSet) (t : List Region) : Prop := ∃ r, r ∈ t ∧ P r = false

/-! ## Certificates

A certificate is a derivation of `Cert P H p K`, read as: if the app starts with
capabilities contained in `H`, then running `p` touches only regions allowed by
the policy `P`, and ends with capabilities contained in `K`. -/
inductive Cert (P : CapSet) : CapSet → Prog → CapSet → Prop where
  | nop (H : CapSet) : Cert P H .nop H
  | acquire (H : CapSet) (r : Region) : Cert P H (.acquire r) (insertCap r H)
  | release (H : CapSet) (r : Region) : Cert P H (.release r) (eraseCap r H)
  | access (H : CapSet) (r : Region) (h : H r = true → P r = true) :
      Cert P H (.access r) H
  | seq {H K L : CapSet} {p q : Prog} :
      Cert P H p K → Cert P K q L → Cert P H (.seq p q) L
  | choice {H K₁ K₂ : CapSet} {p q : Prog} :
      Cert P H p K₁ → Cert P H q K₂ → Cert P H (.choice p q) (unionCap K₁ K₂)
  | conseq {H H' K K' : CapSet} {p : Prog} :
      CapSub H' H → Cert P H p K → CapSub K K' → Cert P H' p K'

/-- **Soundness of certificates.** A certified program, started with capabilities
inside its precondition, only touches regions allowed by the policy, and ends
inside its postcondition. -/
theorem cert_sound {P H K : CapSet} {p : Prog} (c : Cert P H p K) :
    ∀ {h h' : CapSet} {t : List Region}, CapSub h H → Exec p h h' t →
      (∀ r, r ∈ t → P r = true) ∧ CapSub h' K := by
  induction c with
  | nop H =>
      intro h h' t hsub e
      cases e
      exact ⟨by simp, hsub⟩
  | acquire H r =>
      intro h h' t hsub e
      cases e
      exact ⟨by simp, insertCap_mono hsub r⟩
  | release H r =>
      intro h h' t hsub e
      cases e
      exact ⟨by simp, eraseCap_mono hsub r⟩
  | access H r hr =>
      intro h h' t hsub e
      cases e with
      | accessOk _ _ hmem =>
          refine ⟨?_, hsub⟩
          intro s hs
          simp only [List.mem_singleton] at hs
          subst hs
          exact hr (hsub s hmem)
      | accessDenied _ _ _ => exact ⟨by simp, hsub⟩
  | seq c₁ c₂ ih₁ ih₂ =>
      intro h h' t hsub e
      cases e with
      | seq e₁ e₂ =>
          obtain ⟨ht₁, hs₁⟩ := ih₁ hsub e₁
          obtain ⟨ht₂, hs₂⟩ := ih₂ hs₁ e₂
          refine ⟨?_, hs₂⟩
          intro s hs
          rcases List.mem_append.mp hs with hs | hs
          · exact ht₁ s hs
          · exact ht₂ s hs
  | choice c₁ c₂ ih₁ ih₂ =>
      intro h h' t hsub e
      cases e with
      | choiceL e =>
          obtain ⟨ht, hs⟩ := ih₁ hsub e
          exact ⟨ht, fun x hx => mem_unionCap.mpr (Or.inl (hs x hx))⟩
      | choiceR e =>
          obtain ⟨ht, hs⟩ := ih₂ hsub e
          exact ⟨ht, fun x hx => mem_unionCap.mpr (Or.inr (hs x hx))⟩
  | conseq hHH c hKK ih =>
      intro h h' t hsub e
      obtain ⟨ht, hs⟩ := ih (fun x hx => hHH x (hsub x hx)) e
      exact ⟨ht, fun x hx => hKK x (hs x hx)⟩

/-! ## The engine's checker

`analyze p H` computes the capabilities that may be held after running `p` from
capabilities `H` (exactly: see `analyze_reachable`); `check P p H` is the
decidable acceptance test. -/
def analyze : Prog → CapSet → CapSet
  | .nop, H => H
  | .acquire r, H => insertCap r H
  | .release r, H => eraseCap r H
  | .access _, H => H
  | .seq p q, H => analyze q (analyze p H)
  | .choice p q, H => unionCap (analyze p H) (analyze q H)

/-- The isolation engine's decidable checker. -/
def check (P : CapSet) : Prog → CapSet → Bool
  | .nop, _ => true
  | .acquire _, _ => true
  | .release _, _ => true
  | .access r, H => !(H r) || P r
  | .seq p q, H => check P p H && check P q (analyze p H)
  | .choice p q, H => check P p H && check P q H

/-- **Certificate synthesis.** If the checker accepts, the engine can build a
certificate for the app: `Clean → Proved`. -/
theorem check_cert (P : CapSet) : ∀ (p : Prog) (H : CapSet),
    check P p H = true → Cert P H p (analyze p H) := by
  intro p
  induction p with
  | nop => intro H _; exact .nop H
  | acquire r => intro H _; exact .acquire H r
  | release r => intro H _; exact .release H r
  | access r =>
      intro H hc
      refine .access H r ?_
      intro hH
      simp [check, hH] at hc
      exact hc
  | seq p q ihp ihq =>
      intro H hc
      simp only [check, Bool.and_eq_true] at hc
      exact .seq (ihp H hc.1) (ihq (analyze p H) hc.2)
  | choice p q ihp ihq =>
      intro H hc
      simp only [check, Bool.and_eq_true] at hc
      exact .choice (ihp H hc.1) (ihq H hc.2)

/-! ## Exactness of the analysis

The two transfer lemmas below say that the analysis is not merely a sound
over-approximation: anything it predicts is genuinely realisable by a run. -/

/-- Transfer of a *held capability* to a smaller initial capability set. -/
theorem exec_transfer_state {p : Prog} {A c : CapSet} {t : List Region}
    (hx : Exec p A c t) :
    ∀ (r : Region) (B : CapSet), c r = true → (A r = true → B r = true) →
      ∃ b t', Exec p B b t' ∧ b r = true := by
  induction hx with
  | nop h => intro r B hc hAB; exact ⟨B, [], .nop B, hAB hc⟩
  | acquire s h =>
      intro r B hc hAB
      refine ⟨insertCap s B, [], .acquire s B, ?_⟩
      rcases mem_insertCap.mp hc with hc | hc
      · exact mem_insertCap.mpr (Or.inl hc)
      · exact mem_insertCap.mpr (Or.inr (hAB hc))
  | release s h =>
      intro r B hc hAB
      refine ⟨eraseCap s B, [], .release s B, ?_⟩
      rcases mem_eraseCap.mp hc with ⟨h1, h2⟩
      exact mem_eraseCap.mpr ⟨h1, hAB h2⟩
  | accessOk s h hs =>
      intro r B hc hAB
      obtain ⟨b, t', e⟩ := exec_progress (.access s) B
      refine ⟨b, t', e, ?_⟩
      cases e <;> exact hAB hc
  | accessDenied s h hs =>
      intro r B hc hAB
      obtain ⟨b, t', e⟩ := exec_progress (.access s) B
      refine ⟨b, t', e, ?_⟩
      cases e <;> exact hAB hc
  | seq e₁ e₂ ih₁ ih₂ =>
      rename_i p q h h₁ h₂ t₁ t₂
      intro r B hc hAB
      by_cases hm : h₁ r = true
      · obtain ⟨b₁, t₁', ex₁, hb₁⟩ := ih₁ r B hm hAB
        obtain ⟨b, t₂', ex₂, hb⟩ := ih₂ r b₁ hc (fun _ => hb₁)
        exact ⟨b, t₁' ++ t₂', .seq ex₁ ex₂, hb⟩
      · obtain ⟨b₁, t₁', ex₁⟩ := exec_progress p B
        obtain ⟨b, t₂', ex₂, hb⟩ := ih₂ r b₁ hc (fun hh => absurd hh hm)
        exact ⟨b, t₁' ++ t₂', .seq ex₁ ex₂, hb⟩
  | choiceL e ih =>
      intro r B hc hAB
      obtain ⟨b, t', ex, hb⟩ := ih r B hc hAB
      exact ⟨b, t', .choiceL ex, hb⟩
  | choiceR e ih =>
      intro r B hc hAB
      obtain ⟨b, t', ex, hb⟩ := ih r B hc hAB
      exact ⟨b, t', .choiceR ex, hb⟩

/-- Transfer of an *observed access* to a smaller initial capability set. -/
theorem exec_transfer_trace {p : Prog} {A c : CapSet} {t : List Region}
    (hx : Exec p A c t) :
    ∀ (r : Region) (B : CapSet), r ∈ t → (A r = true → B r = true) →
      ∃ b t', Exec p B b t' ∧ r ∈ t' := by
  induction hx with
  | nop h => intro r B hr _; simp at hr
  | acquire s h => intro r B hr _; simp at hr
  | release s h => intro r B hr _; simp at hr
  | accessOk s h hs =>
      intro r B hr hAB
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨B, [r], .accessOk r B (hAB hs), by simp⟩
  | accessDenied s h hs => intro r B hr _; simp at hr
  | seq e₁ e₂ ih₁ ih₂ =>
      rename_i p q h h₁ h₂ t₁ t₂
      intro r B hr hAB
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨b₁, t₁', ex₁, hb₁⟩ := ih₁ r B hr hAB
        obtain ⟨b, t₂', ex₂⟩ := exec_progress q b₁
        exact ⟨b, t₁' ++ t₂', .seq ex₁ ex₂, by simp [hb₁]⟩
      · by_cases hm : h₁ r = true
        · obtain ⟨b₁, t₁', ex₁, hb₁⟩ := exec_transfer_state e₁ r B hm hAB
          obtain ⟨b, t₂', ex₂, hb⟩ := ih₂ r b₁ hr (fun _ => hb₁)
          exact ⟨b, t₁' ++ t₂', .seq ex₁ ex₂, by simp [hb]⟩
        · obtain ⟨b₁, t₁', ex₁⟩ := exec_progress p B
          obtain ⟨b, t₂', ex₂, hb⟩ := ih₂ r b₁ hr (fun hh => absurd hh hm)
          exact ⟨b, t₁' ++ t₂', .seq ex₁ ex₂, by simp [hb]⟩
  | choiceL e ih =>
      intro r B hr hAB
      obtain ⟨b, t', ex, hb⟩ := ih r B hr hAB
      exact ⟨b, t', .choiceL ex, hb⟩
  | choiceR e ih =>
      intro r B hr hAB
      obtain ⟨b, t', ex, hb⟩ := ih r B hr hAB
      exact ⟨b, t', .choiceR ex, hb⟩

/-- **Exactness of the analysis**: every capability predicted by `analyze` is
really held after some run. -/
theorem analyze_reachable : ∀ (p : Prog) (H : CapSet) (r : Region),
    analyze p H r = true → ∃ h' t, Exec p H h' t ∧ h' r = true := by
  intro p
  induction p with
  | nop => intro H r hr; exact ⟨H, [], .nop H, hr⟩
  | acquire s => intro H r hr; exact ⟨insertCap s H, [], .acquire s H, hr⟩
  | release s => intro H r hr; exact ⟨eraseCap s H, [], .release s H, hr⟩
  | access s =>
      intro H r hr
      obtain ⟨h', t, e⟩ := exec_progress (.access s) H
      refine ⟨h', t, e, ?_⟩
      cases e <;> exact hr
  | seq p q ihp ihq =>
      intro H r hr
      obtain ⟨m, tm, exm, hm⟩ := ihq (analyze p H) r hr
      by_cases hp : analyze p H r = true
      · obtain ⟨h₁, t₁, ex₁, h₁r⟩ := ihp H r hp
        obtain ⟨b, t₂, ex₂, hb⟩ := exec_transfer_state exm r h₁ hm (fun _ => h₁r)
        exact ⟨b, t₁ ++ t₂, .seq ex₁ ex₂, hb⟩
      · obtain ⟨h₁, t₁, ex₁⟩ := exec_progress p H
        obtain ⟨b, t₂, ex₂, hb⟩ := exec_transfer_state exm r h₁ hm (fun hh => absurd hh hp)
        exact ⟨b, t₁ ++ t₂, .seq ex₁ ex₂, hb⟩
  | choice p q ihp ihq =>
      intro H r hr
      rcases mem_unionCap.mp hr with hr | hr
      · obtain ⟨h', t, e, hh⟩ := ihp H r hr
        exact ⟨h', t, .choiceL e, hh⟩
      · obtain ⟨h', t, e, hh⟩ := ihq H r hr
        exact ⟨h', t, .choiceR e, hh⟩

/-- **Completeness of the checker.** If the engine rejects the app, then the app
really does have a run that escapes its policy. -/
theorem check_complete (P : CapSet) : ∀ (p : Prog) (H : CapSet),
    check P p H = false → ∃ h' t, Exec p H h' t ∧ EscapingTrace P t := by
  intro p
  induction p with
  | nop => intro H hc; simp [check] at hc
  | acquire r => intro H hc; simp [check] at hc
  | release r => intro H hc; simp [check] at hc
  | access r =>
      intro H hc
      simp only [check, Bool.or_eq_false_iff, Bool.not_eq_false'] at hc
      exact ⟨H, [r], .accessOk r H hc.1, ⟨r, by simp, hc.2⟩⟩
  | seq p q ihp ihq =>
      intro H hc
      simp only [check, Bool.and_eq_false_iff] at hc
      rcases hc with hc | hc
      · obtain ⟨h₁, t₁, ex₁, r, hr, hP⟩ := ihp H hc
        obtain ⟨h₂, t₂, ex₂⟩ := exec_progress q h₁
        exact ⟨h₂, t₁ ++ t₂, .seq ex₁ ex₂, ⟨r, by simp [hr], hP⟩⟩
      · obtain ⟨m, tm, exm, r, hr, hP⟩ := ihq (analyze p H) hc
        by_cases hpr : analyze p H r = true
        · obtain ⟨h₁, t₁, ex₁, h₁r⟩ := analyze_reachable p H r hpr
          obtain ⟨b, t₂, ex₂, hb⟩ := exec_transfer_trace exm r h₁ hr (fun _ => h₁r)
          exact ⟨b, t₁ ++ t₂, .seq ex₁ ex₂, ⟨r, by simp [hb], hP⟩⟩
        · obtain ⟨h₁, t₁, ex₁⟩ := exec_progress p H
          obtain ⟨b, t₂, ex₂, hb⟩ := exec_transfer_trace exm r h₁ hr (fun hh => absurd hh hpr)
          exact ⟨b, t₁ ++ t₂, .seq ex₁ ex₂, ⟨r, by simp [hb], hP⟩⟩
  | choice p q ihp ihq =>
      intro H hc
      simp only [check, Bool.and_eq_false_iff] at hc
      rcases hc with hc | hc
      · obtain ⟨h', t, e, esc⟩ := ihp H hc
        exact ⟨h', t, .choiceL e, esc⟩
      · obtain ⟨h', t, e, esc⟩ := ihq H hc
        exact ⟨h', t, .choiceR e, esc⟩

/-! ## Applications and the isolation guarantee -/

/-- A proof-carrying application: its sandbox policy, the capabilities it starts
with, and its code. -/
structure App where
  /-- The sandbox boundary: the regions the app is allowed to touch. -/
  policy : CapSet
  /-- The capabilities the app starts with. -/
  init : CapSet
  /-- The app's code. -/
  code : Prog

/-- The app has a run that observably touches a region outside its policy. -/
def App.Escapes (a : App) : Prop :=
  ∃ h' t, Exec a.code a.init h' t ∧ EscapingTrace a.policy t

/-- The engine's checker accepts the app. -/
def App.Clean (a : App) : Prop := check a.policy a.code a.init = true

/-- The app carries a valid capability certificate. -/
def App.Proved (a : App) : Prop := ∃ K, Cert a.policy a.init a.code K

/-- The app is accepted by the engine *and* carries a valid certificate. -/
def App.CleanProved (a : App) : Prop := a.Clean ∧ a.Proved

/-- A certified app cannot escape its sandbox. -/
theorem proved_no_escape (a : App) (h : a.Proved) : ¬ a.Escapes := by
  obtain ⟨K, c⟩ := h
  rintro ⟨h', t, e, r, hr, hP⟩
  have hPt := (cert_sound c (CapSub.refl a.init) e).1 r hr
  rw [hPt] at hP
  exact Bool.noConfusion hP

/-- An app accepted by the engine cannot escape its sandbox. -/
theorem clean_no_escape (a : App) (h : a.Clean) : ¬ a.Escapes :=
  proved_no_escape a ⟨_, check_cert a.policy a.code a.init h⟩

/-- Conversely, an app with no escaping run is accepted and certifiable. -/
theorem no_escape_cleanProved (a : App) (h : ¬ a.Escapes) : a.CleanProved := by
  have hclean : a.Clean := by
    unfold App.Clean
    cases hc : check a.policy a.code a.init with
    | true => rfl
    | false =>
        obtain ⟨h', t, e, esc⟩ := check_complete a.policy a.code a.init hc
        exact absurd ⟨h', t, e, esc⟩ h
  exact ⟨hclean, ⟨_, check_cert a.policy a.code a.init hclean⟩⟩

/-- **Target theorem.** No application can be simultaneously accepted by the
isolation engine's checker, carry a valid capability certificate, and still have
a run that escapes its sandbox policy. -/
theorem no_clean_proved_with_escape : ¬ ∃ a : App, a.CleanProved ∧ a.Escapes := by
  rintro ⟨a, ⟨_, hproved⟩, hesc⟩
  exact proved_no_escape a hproved hesc

/-- **Soundness and completeness of the isolation engine's model.** An app is
accepted-and-certified exactly when it has no escaping run. -/
theorem clean_proved_iff_no_escape (a : App) : a.CleanProved ↔ ¬ a.Escapes :=
  ⟨fun h => proved_no_escape a h.2, no_escape_cleanProved a⟩

/-! ## Non-vacuity: the model has both escaping and safe applications -/

/-- A sandbox policy that allows only region `0`. -/
def demoPolicy : CapSet := fun r => r == 0

/-- The empty capability set. -/
def noCaps : CapSet := fun _ => false

/-- An app that grabs a capability outside its sandbox and uses it. -/
def rogueApp : App := ⟨demoPolicy, noCaps, .seq (.acquire 1) (.access 1)⟩

theorem rogueApp_escapes : rogueApp.Escapes :=
  ⟨insertCap 1 noCaps, [] ++ [1],
    .seq (.acquire 1 noCaps) (.accessOk 1 (insertCap 1 noCaps) (by decide)),
    ⟨1, by simp, by decide⟩⟩

theorem rogueApp_not_cleanProved : ¬ rogueApp.CleanProved := fun h =>
  (clean_proved_iff_no_escape rogueApp).mp h rogueApp_escapes

/-- An app that stays inside its sandbox. -/
def goodApp : App := ⟨demoPolicy, noCaps, .seq (.acquire 0) (.access 0)⟩

theorem goodApp_clean : goodApp.Clean := by
  show check demoPolicy goodApp.code goodApp.init = true
  decide

theorem goodApp_cleanProved : goodApp.CleanProved :=
  ⟨goodApp_clean, ⟨_, check_cert _ _ _ goodApp_clean⟩⟩

theorem goodApp_not_escapes : ¬ goodApp.Escapes :=
  (clean_proved_iff_no_escape goodApp).mp goodApp_cleanProved

/-- Mediation matters: an access to a forbidden region whose capability is not
held is denied by the engine, so such an app is still safe. -/
def deniedApp : App := ⟨demoPolicy, noCaps, .access 1⟩

theorem deniedApp_clean : deniedApp.Clean := by
  show check demoPolicy deniedApp.code deniedApp.init = true
  decide

theorem deniedApp_cleanProved : deniedApp.CleanProved :=
  ⟨deniedApp_clean, ⟨_, check_cert _ _ _ deniedApp_clean⟩⟩

end PCA.Isolation

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

