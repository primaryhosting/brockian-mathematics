import Mathlib
import RequestProject.NoCleanProvedWithEscape

/-!
# A structured isolation engine with control flow

`RequestProject.NoCleanProvedWithEscape` models straight-line applications. Here the
application language has real control flow, so the static verifier is a genuine
*must-hold* capability analysis rather than a single pass over a list:

* `Cmd` : commands built from `use`, `grant`, `revoke`, sequencing, nondeterministic
  branching (an `if` whose guard the verifier cannot predict) and loops (`loop`, executed
  any number of times);
* `Ok policy c g g'` : an execution of `c` from capability set `g` that stays inside the
  sandbox and ends holding `g'`;
* `Fail policy c g` : an execution of `c` from `g` that crosses the sandbox boundary — this
  is what `EscapesS` means;
* `analyze` : the static verifier. It computes a *lower bound* on the capabilities that are
  certainly held: branches are merged by intersection, and a loop is admitted only when its
  body preserves the capabilities held on entry;
* `DerivS` : the certificate logic; `ProvedS` means a certificate exists.

Main results:

* `analyze_eq_some_iff_derivS` : the verifier decides the certificate logic (`cleanS_iff_provedS`);
* `analyze_sound_ok` : whatever an accepted command actually produces contains the analyzed
  lower bound (the analysis is a correct must-analysis);
* `soundS` : an accepted command can never fail, i.e. never escapes;
* `no_clean_proved_with_escapeS` : the target statement for this richer engine;
* `ok_subset_union_policy` : confinement / least privilege — a sandboxed execution never holds
  more than its initial capabilities together with the policy;
* `analyze_policy_mono`, `cleanS_of_policy_subset` : widening the policy never invalidates a
  certificate;
* `cleanS_iff_no_escapeS_det` : on the deterministic fragment the verifier is exact.

Note the verifier is *not* complete here, and that is a feature of the model rather than a
defect: `analyze_incomplete` exhibits a command that can never escape yet is rejected,
because the analysis must be conservative about unpredictable branching.
-/

namespace PCA
namespace Isolation
namespace Structured

/-- Applications with control flow. -/
inductive Cmd : Type
  /-- Perform an effect requiring capability `c`. -/
  | use (c : Cap) : Cmd
  /-- Acquire capability `c` from the sandbox. -/
  | grant (c : Cap) : Cmd
  /-- Voluntarily drop capability `c`. -/
  | revoke (c : Cap) : Cmd
  /-- Sequential composition. -/
  | seq (a b : Cmd) : Cmd
  /-- Branch on a guard the verifier cannot predict. -/
  | choice (a b : Cmd) : Cmd
  /-- Repeat a body any number of times. -/
  | loop (a : Cmd) : Cmd
  deriving DecidableEq, Repr

/-- `Ok policy c g g'` : running `c` from capabilities `g` can stay inside the sandbox and
finish holding `g'`. -/
inductive Ok (policy : Finset Cap) : Cmd → Finset Cap → Finset Cap → Prop
  | use {g : Finset Cap} {c : Cap} : c ∈ g → Ok policy (Cmd.use c) g g
  | grant {g : Finset Cap} {c : Cap} : c ∈ policy → Ok policy (Cmd.grant c) g (insert c g)
  | revoke {g : Finset Cap} {c : Cap} : Ok policy (Cmd.revoke c) g (g.erase c)
  | seq {a b : Cmd} {g g₁ g₂ : Finset Cap} :
      Ok policy a g g₁ → Ok policy b g₁ g₂ → Ok policy (Cmd.seq a b) g g₂
  | choiceL {a b : Cmd} {g g' : Finset Cap} : Ok policy a g g' → Ok policy (Cmd.choice a b) g g'
  | choiceR {a b : Cmd} {g g' : Finset Cap} : Ok policy b g g' → Ok policy (Cmd.choice a b) g g'
  | loopDone {a : Cmd} {g : Finset Cap} : Ok policy (Cmd.loop a) g g
  | loopStep {a : Cmd} {g g₁ g₂ : Finset Cap} :
      Ok policy a g g₁ → Ok policy (Cmd.loop a) g₁ g₂ → Ok policy (Cmd.loop a) g g₂

/-- `Fail policy c g` : running `c` from capabilities `g` can cross the sandbox boundary. -/
inductive Fail (policy : Finset Cap) : Cmd → Finset Cap → Prop
  | use {g : Finset Cap} {c : Cap} : c ∉ g → Fail policy (Cmd.use c) g
  | grant {g : Finset Cap} {c : Cap} : c ∉ policy → Fail policy (Cmd.grant c) g
  | seqL {a b : Cmd} {g : Finset Cap} : Fail policy a g → Fail policy (Cmd.seq a b) g
  | seqR {a b : Cmd} {g g₁ : Finset Cap} :
      Ok policy a g g₁ → Fail policy b g₁ → Fail policy (Cmd.seq a b) g
  | choiceL {a b : Cmd} {g : Finset Cap} : Fail policy a g → Fail policy (Cmd.choice a b) g
  | choiceR {a b : Cmd} {g : Finset Cap} : Fail policy b g → Fail policy (Cmd.choice a b) g
  | loopHere {a : Cmd} {g : Finset Cap} : Fail policy a g → Fail policy (Cmd.loop a) g
  | loopStep {a : Cmd} {g g₁ : Finset Cap} :
      Ok policy a g g₁ → Fail policy (Cmd.loop a) g₁ → Fail policy (Cmd.loop a) g

/-- The static verifier: a must-analysis returning a lower bound on the capabilities held
after the command, or `none` if the command may breach the sandbox. -/
def analyze (policy : Finset Cap) : Cmd → Finset Cap → Option (Finset Cap)
  | Cmd.use c, g => if c ∈ g then some g else none
  | Cmd.grant c, g => if c ∈ policy then some (insert c g) else none
  | Cmd.revoke c, g => some (g.erase c)
  | Cmd.seq a b, g => (analyze policy a g).bind (fun g₁ => analyze policy b g₁)
  | Cmd.choice a b, g =>
      (analyze policy a g).bind (fun g₁ => (analyze policy b g).map (fun g₂ => g₁ ∩ g₂))
  | Cmd.loop a, g => (analyze policy a g).bind (fun ga => if g ⊆ ga then some g else none)

/-- The certificate logic for structured applications. -/
inductive DerivS (policy : Finset Cap) : Cmd → Finset Cap → Finset Cap → Prop
  | use {g : Finset Cap} {c : Cap} : c ∈ g → DerivS policy (Cmd.use c) g g
  | grant {g : Finset Cap} {c : Cap} : c ∈ policy → DerivS policy (Cmd.grant c) g (insert c g)
  | revoke {g : Finset Cap} {c : Cap} : DerivS policy (Cmd.revoke c) g (g.erase c)
  | seq {a b : Cmd} {g g₁ g₂ : Finset Cap} :
      DerivS policy a g g₁ → DerivS policy b g₁ g₂ → DerivS policy (Cmd.seq a b) g g₂
  | choice {a b : Cmd} {g g₁ g₂ : Finset Cap} :
      DerivS policy a g g₁ → DerivS policy b g g₂ → DerivS policy (Cmd.choice a b) g (g₁ ∩ g₂)
  | loop {a : Cmd} {g ga : Finset Cap} :
      DerivS policy a g ga → g ⊆ ga → DerivS policy (Cmd.loop a) g g

/-- The application escapes: some execution crosses the sandbox boundary. -/
def EscapesS (policy : Finset Cap) (c : Cmd) (g : Finset Cap) : Prop := Fail policy c g

/-- The application is accepted by the verifier. -/
def CleanS (policy : Finset Cap) (c : Cmd) (g : Finset Cap) : Prop :=
  ∃ g' : Finset Cap, analyze policy c g = some g'

/-- The application carries a certificate. -/
def ProvedS (policy : Finset Cap) (c : Cmd) (g : Finset Cap) : Prop :=
  ∃ g' : Finset Cap, Nonempty (DerivS policy c g g')

/-! ### The verifier decides the certificate logic -/

theorem derivS_of_analyze {policy : Finset Cap} :
    ∀ (c : Cmd) (g g' : Finset Cap), analyze policy c g = some g' → DerivS policy c g g'
  | Cmd.use d, g, g', h => by
      by_cases hd : d ∈ g
      · simp only [analyze, if_pos hd, Option.some.injEq] at h
        subst h; exact DerivS.use hd
      · simp [analyze, hd] at h
  | Cmd.grant d, g, g', h => by
      by_cases hd : d ∈ policy
      · simp only [analyze, if_pos hd, Option.some.injEq] at h
        subst h; exact DerivS.grant hd
      · simp [analyze, hd] at h
  | Cmd.revoke d, g, g', h => by
      simp only [analyze, Option.some.injEq] at h
      subst h; exact DerivS.revoke
  | Cmd.seq a b, g, g', h => by
      simp only [analyze, Option.bind_eq_some_iff] at h
      obtain ⟨g₁, h₁, h₂⟩ := h
      exact DerivS.seq (derivS_of_analyze a g g₁ h₁) (derivS_of_analyze b g₁ g' h₂)
  | Cmd.choice a b, g, g', h => by
      simp only [analyze, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨g₁, h₁, g₂, h₂, h₃⟩ := h
      subst h₃
      exact DerivS.choice (derivS_of_analyze a g g₁ h₁) (derivS_of_analyze b g g₂ h₂)
  | Cmd.loop a, g, g', h => by
      simp only [analyze, Option.bind_eq_some_iff] at h
      obtain ⟨ga, ha, hb⟩ := h
      by_cases hsub : g ⊆ ga
      · rw [if_pos hsub] at hb
        cases hb
        exact DerivS.loop (derivS_of_analyze a g ga ha) hsub
      · rw [if_neg hsub] at hb
        exact absurd hb (by simp)

theorem analyze_of_derivS {policy : Finset Cap} {c : Cmd} {g g' : Finset Cap}
    (d : DerivS policy c g g') : analyze policy c g = some g' := by
  induction d with
  | use hc => simp [analyze, hc]
  | grant hc => simp [analyze, hc]
  | revoke => simp [analyze]
  | seq _ _ ih₁ ih₂ => simp [analyze, ih₁, ih₂]
  | choice _ _ ih₁ ih₂ => simp [analyze, ih₁, ih₂]
  | loop _ hsub ih => simp [analyze, ih, hsub]

/-- The verifier is exactly a decision procedure for the certificate logic. -/
theorem analyze_eq_some_iff_derivS {policy : Finset Cap} {c : Cmd} {g g' : Finset Cap} :
    analyze policy c g = some g' ↔ DerivS policy c g g' :=
  ⟨derivS_of_analyze c g g', analyze_of_derivS⟩

theorem cleanS_iff_provedS {policy : Finset Cap} {c : Cmd} {g : Finset Cap} :
    CleanS policy c g ↔ ProvedS policy c g := by
  constructor
  · rintro ⟨g', h⟩
    exact ⟨g', ⟨derivS_of_analyze c g g' h⟩⟩
  · rintro ⟨g', ⟨d⟩⟩
    exact ⟨g', analyze_of_derivS d⟩

/-! ### The analysis is a correct must-analysis -/

/-- Whatever an accepted command actually produces contains the analyzed lower bound, even
when the analysis was performed on a smaller (under-approximated) capability set. -/
theorem analyze_sound_ok {policy : Finset Cap} {c : Cmd} {G G₂ : Finset Cap}
    (hok : Ok policy c G G₂) :
    ∀ {g g' : Finset Cap}, g ⊆ G → analyze policy c g = some g' → g' ⊆ G₂ := by
  induction hok with
  | @use G d hd =>
      intro g g' hsub h
      by_cases hg : d ∈ g
      · simp only [analyze, if_pos hg, Option.some.injEq] at h
        exact h ▸ hsub
      · simp [analyze, hg] at h
  | @grant G d hd =>
      intro g g' hsub h
      by_cases hg : d ∈ policy
      · simp only [analyze, if_pos hg, Option.some.injEq] at h
        subst h
        exact Finset.insert_subset_insert _ hsub
      · simp [analyze, hg] at h
  | @revoke G d =>
      intro g g' hsub h
      simp only [analyze, Option.some.injEq] at h
      subst h
      exact Finset.erase_subset_erase _ hsub
  | @seq a b G G₁ G₂ _ _ iha ihb =>
      intro g g' hsub h
      simp only [analyze, Option.bind_eq_some_iff] at h
      obtain ⟨g₁, h₁, h₂⟩ := h
      exact ihb (iha hsub h₁) h₂
  | @choiceL a b G G' _ iha =>
      intro g g' hsub h
      simp only [analyze, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨g₁, h₁, g₂, _, h₃⟩ := h
      subst h₃
      exact (Finset.inter_subset_left).trans (iha hsub h₁)
  | @choiceR a b G G' _ ihb =>
      intro g g' hsub h
      simp only [analyze, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨g₁, _, g₂, h₂, h₃⟩ := h
      subst h₃
      exact (Finset.inter_subset_right).trans (ihb hsub h₂)
  | @loopDone a G =>
      intro g g' hsub h
      simp only [analyze, Option.bind_eq_some_iff] at h
      obtain ⟨ga, _, hb⟩ := h
      by_cases hs : g ⊆ ga
      · rw [if_pos hs, Option.some.injEq] at hb
        exact hb ▸ hsub
      · rw [if_neg hs] at hb
        exact absurd hb (by simp)
  | @loopStep a G G₁ G₂ _ _ iha ihloop =>
      intro g g' hsub h
      have h' := h
      simp only [analyze, Option.bind_eq_some_iff] at h'
      obtain ⟨ga, ha, hb⟩ := h'
      by_cases hs : g ⊆ ga
      · rw [if_pos hs, Option.some.injEq] at hb
        subst hb
        exact ihloop ((hs.trans (iha hsub ha))) h
      · rw [if_neg hs] at hb
        exact absurd hb (by simp)

/-! ### Soundness: an accepted application cannot escape -/

theorem not_fail_of_analyze {policy : Finset Cap} {c : Cmd} {G : Finset Cap}
    (hfail : Fail policy c G) :
    ∀ {g g' : Finset Cap}, g ⊆ G → analyze policy c g = some g' → False := by
  induction hfail with
  | @use G d hd =>
      intro g g' hsub h
      by_cases hg : d ∈ g
      · exact hd (hsub hg)
      · simp [analyze, hg] at h
  | @grant G d hd =>
      intro g g' hsub h
      simp [analyze, hd] at h
  | @seqL a b G _ iha =>
      intro g g' hsub h
      simp only [analyze, Option.bind_eq_some_iff] at h
      obtain ⟨g₁, h₁, _⟩ := h
      exact iha hsub h₁
  | @seqR a b G G₁ hoka _ ihb =>
      intro g g' hsub h
      simp only [analyze, Option.bind_eq_some_iff] at h
      obtain ⟨g₁, h₁, h₂⟩ := h
      exact ihb (analyze_sound_ok hoka hsub h₁) h₂
  | @choiceL a b G _ iha =>
      intro g g' hsub h
      simp only [analyze, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨g₁, h₁, _⟩ := h
      exact iha hsub h₁
  | @choiceR a b G _ ihb =>
      intro g g' hsub h
      simp only [analyze, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, g₂, h₂, _⟩ := h
      exact ihb hsub h₂
  | @loopHere a G _ iha =>
      intro g g' hsub h
      simp only [analyze, Option.bind_eq_some_iff] at h
      obtain ⟨ga, ha, _⟩ := h
      exact iha hsub ha
  | @loopStep a G G₁ hoka _ ihloop =>
      intro g g' hsub h
      have h' := h
      simp only [analyze, Option.bind_eq_some_iff] at h'
      obtain ⟨ga, ha, hb⟩ := h'
      by_cases hs : g ⊆ ga
      · rw [if_pos hs, Option.some.injEq] at hb
        subst hb
        exact ihloop (hs.trans (analyze_sound_ok hoka hsub ha)) h
      · rw [if_neg hs] at hb
        exact absurd hb (by simp)

/-- **Soundness** for the structured engine: an accepted application never escapes. -/
theorem soundS {policy : Finset Cap} {c : Cmd} {g : Finset Cap} (hclean : CleanS policy c g) :
    ¬ EscapesS policy c g := by
  rintro hfail
  obtain ⟨g', h⟩ := hclean
  exact not_fail_of_analyze hfail (subset_refl g) h

/-- **The target statement for the structured engine.** No application is simultaneously
accepted by the verifier, certified, and able to escape the sandbox. -/
theorem no_clean_proved_with_escapeS (policy : Finset Cap) (c : Cmd) (g : Finset Cap) :
    ¬ (CleanS policy c g ∧ ProvedS policy c g ∧ EscapesS policy c g) := by
  rintro ⟨hclean, -, hesc⟩
  exact soundS hclean hesc

/-- A certified application is also escape-free, stated directly from the certificate. -/
theorem no_escape_of_provedS {policy : Finset Cap} {c : Cmd} {g : Finset Cap}
    (hproved : ProvedS policy c g) : ¬ EscapesS policy c g :=
  soundS (cleanS_iff_provedS.mpr hproved)

/-! ### Confinement and policy monotonicity -/

/-- **Confinement / least privilege**: an execution that stays inside the sandbox never holds
anything beyond the capabilities it started with together with those the policy permits. -/
theorem ok_subset_union_policy {policy : Finset Cap} {c : Cmd} {g G : Finset Cap}
    (h : Ok policy c g G) : G ⊆ g ∪ policy := by
  induction h with
  | use _ => exact Finset.subset_union_left
  | grant hc => exact Finset.insert_subset (Finset.mem_union_right _ hc) Finset.subset_union_left
  | revoke => exact (Finset.erase_subset _ _).trans Finset.subset_union_left
  | seq _ _ ih₁ ih₂ =>
      exact ih₂.trans (Finset.union_subset ih₁ Finset.subset_union_right)
  | choiceL _ ih => exact ih
  | choiceR _ ih => exact ih
  | loopDone => exact Finset.subset_union_left
  | loopStep _ _ ih₁ ih₂ =>
      exact ih₂.trans (Finset.union_subset ih₁ Finset.subset_union_right)

/-- **Relaxing the sandbox policy never invalidates a certificate**: an accepted application
is still accepted, with the very same analysis result, under any wider policy. -/
theorem analyze_policy_mono {policy policy' : Finset Cap} (hp : policy ⊆ policy') :
    ∀ (c : Cmd) (g g' : Finset Cap),
      analyze policy c g = some g' → analyze policy' c g = some g'
  | Cmd.use d, g, g', h => by
      by_cases hd : d ∈ g
      · simpa [analyze, hd] using h
      · simp [analyze, hd] at h
  | Cmd.grant d, g, g', h => by
      by_cases hd : d ∈ policy
      · simpa [analyze, hd, hp hd] using h
      · simp [analyze, hd] at h
  | Cmd.revoke d, g, g', h => by simpa [analyze] using h
  | Cmd.seq a b, g, g', h => by
      simp only [analyze, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨g₁, h₁, h₂⟩ := h
      exact ⟨g₁, analyze_policy_mono hp a g g₁ h₁, analyze_policy_mono hp b g₁ g' h₂⟩
  | Cmd.choice a b, g, g', h => by
      simp only [analyze, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨g₁, h₁, g₂, h₂, h₃⟩ := h
      exact ⟨g₁, analyze_policy_mono hp a g g₁ h₁, g₂, analyze_policy_mono hp b g g₂ h₂, h₃⟩
  | Cmd.loop a, g, g', h => by
      simp only [analyze, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨ga, ha, hb⟩ := h
      exact ⟨ga, analyze_policy_mono hp a g ga ha, hb⟩

/-- Consequence: cleanliness is monotone in the policy. -/
theorem cleanS_of_policy_subset {policy policy' : Finset Cap} {c : Cmd} {g : Finset Cap}
    (hp : policy ⊆ policy') (hclean : CleanS policy c g) : CleanS policy' c g := by
  obtain ⟨g', h⟩ := hclean
  exact ⟨g', analyze_policy_mono hp c g g' h⟩

/-! ### Completeness on the deterministic fragment

The verifier is incomplete in general (see `analyze_incomplete` below), but on applications
without unpredictable branching or loops it is exact: there it rejects precisely the
applications that really can escape. -/

/-- Applications without branching or loops. -/
def Det : Cmd → Prop
  | Cmd.use _ => True
  | Cmd.grant _ => True
  | Cmd.revoke _ => True
  | Cmd.seq a b => Det a ∧ Det b
  | Cmd.choice _ _ => False
  | Cmd.loop _ => False

/-- On the deterministic fragment the analysis result is actually realised by an execution. -/
theorem ok_of_analyze_det {policy : Finset Cap} :
    ∀ (c : Cmd) (g g' : Finset Cap), Det c → analyze policy c g = some g' → Ok policy c g g'
  | Cmd.use d, g, g', _, h => by
      by_cases hd : d ∈ g
      · simp only [analyze, if_pos hd, Option.some.injEq] at h
        subst h; exact Ok.use hd
      · simp [analyze, hd] at h
  | Cmd.grant d, g, g', _, h => by
      by_cases hd : d ∈ policy
      · simp only [analyze, if_pos hd, Option.some.injEq] at h
        subst h; exact Ok.grant hd
      · simp [analyze, hd] at h
  | Cmd.revoke d, g, g', _, h => by
      simp only [analyze, Option.some.injEq] at h
      subst h; exact Ok.revoke
  | Cmd.seq a b, g, g', hdet, h => by
      simp only [analyze, Option.bind_eq_some_iff] at h
      obtain ⟨g₁, h₁, h₂⟩ := h
      exact Ok.seq (ok_of_analyze_det a g g₁ hdet.1 h₁) (ok_of_analyze_det b g₁ g' hdet.2 h₂)
  | Cmd.choice _ _, _, _, hdet, _ => absurd hdet id
  | Cmd.loop _, _, _, hdet, _ => absurd hdet id

/-- On the deterministic fragment, a rejected application really does escape. -/
theorem fail_of_analyze_none_det {policy : Finset Cap} :
    ∀ (c : Cmd) (g : Finset Cap), Det c → analyze policy c g = none → Fail policy c g
  | Cmd.use d, g, _, h => by
      by_cases hd : d ∈ g
      · simp [analyze, hd] at h
      · exact Fail.use hd
  | Cmd.grant d, g, _, h => by
      by_cases hd : d ∈ policy
      · simp [analyze, hd] at h
      · exact Fail.grant hd
  | Cmd.revoke d, g, _, h => by simp [analyze] at h
  | Cmd.seq a b, g, hdet, h => by
      cases ha : analyze policy a g with
      | none => exact Fail.seqL (fail_of_analyze_none_det a g hdet.1 ha)
      | some g₁ =>
          refine Fail.seqR (ok_of_analyze_det a g g₁ hdet.1 ha)
            (fail_of_analyze_none_det b g₁ hdet.2 ?_)
          simpa [analyze, ha] using h
  | Cmd.choice _ _, _, hdet, _ => absurd hdet id
  | Cmd.loop _, _, hdet, _ => absurd hdet id

/-- **Exactness on the deterministic fragment**: there, clean, proved and escape-free all
coincide. -/
theorem cleanS_iff_no_escapeS_det {policy : Finset Cap} {c : Cmd} {g : Finset Cap}
    (hdet : Det c) : CleanS policy c g ↔ ¬ EscapesS policy c g := by
  refine ⟨soundS, fun hsafe => ?_⟩
  cases h : analyze policy c g with
  | none => exact absurd (fail_of_analyze_none_det c g hdet h) hsafe
  | some g' => exact ⟨g', h⟩

/-! ### The model is not vacuous -/

/-- A loop that uses a granted capability forever is accepted. -/
example : CleanS {1} (Cmd.loop (Cmd.use 1)) {1} := ⟨{1}, by decide⟩

/-- Hence it cannot escape. -/
example : ¬ EscapesS {1} (Cmd.loop (Cmd.use 1)) {1} := soundS ⟨{1}, by decide⟩

/-- A loop whose body revokes the capability it needs is rejected, and indeed it escapes on
the second iteration. -/
example : ¬ CleanS {1} (Cmd.loop (Cmd.seq (Cmd.use 1) (Cmd.revoke 1))) {1} := by
  rintro ⟨g', h⟩
  rw [show analyze {1} (Cmd.loop (Cmd.seq (Cmd.use 1) (Cmd.revoke 1))) {1} = none from by
    decide] at h
  exact absurd h (by simp)

example : EscapesS {1} (Cmd.loop (Cmd.seq (Cmd.use 1) (Cmd.revoke 1))) {1} :=
  Fail.loopStep (Ok.seq (Ok.use (by decide)) Ok.revoke)
    (Fail.loopHere (Fail.seqL (Fail.use (by decide))))

/-- Using a capability that only one branch grants is rejected: the verifier must merge
branches by intersection. -/
example : ¬ CleanS {1} (Cmd.seq (Cmd.choice (Cmd.grant 1) (Cmd.revoke 1)) (Cmd.use 1)) ∅ := by
  rintro ⟨g', h⟩
  rw [show analyze {1} (Cmd.seq (Cmd.choice (Cmd.grant 1) (Cmd.revoke 1)) (Cmd.use 1)) ∅ = none
    from by decide] at h
  exact absurd h (by simp)

/-- A command that neither uses nor acquires capabilities. -/
def Harmless : Cmd → Prop
  | Cmd.use _ => False
  | Cmd.grant _ => False
  | Cmd.revoke _ => True
  | Cmd.seq a b => Harmless a ∧ Harmless b
  | Cmd.choice a b => Harmless a ∧ Harmless b
  | Cmd.loop a => Harmless a

/-- A harmless command can never cross the sandbox boundary. -/
theorem not_fail_of_harmless {policy : Finset Cap} {c : Cmd} {G : Finset Cap}
    (h : Fail policy c G) : ¬ Harmless c := by
  induction h with
  | use _ => exact id
  | grant _ => exact id
  | seqL _ iha => exact fun hh => iha hh.1
  | seqR _ _ ihb => exact fun hh => ihb hh.2
  | choiceL _ iha => exact fun hh => iha hh.1
  | choiceR _ ihb => exact fun hh => ihb hh.2
  | loopHere _ iha => exact iha
  | loopStep _ _ ihloop => exact ihloop

/-- **The verifier is incomplete**, and necessarily so for a language with loops: the
command `loop (revoke 0)` can never escape — it performs no capability use or acquisition at
all — yet the analysis rejects it, because its body does not preserve the capabilities held
on entry. -/
theorem analyze_incomplete :
    ∃ (policy : Finset Cap) (c : Cmd) (g : Finset Cap),
      ¬ EscapesS policy c g ∧ ¬ CleanS policy c g := by
  refine ⟨∅, Cmd.loop (Cmd.revoke 0), {0}, ?_, ?_⟩
  · exact fun hfail => not_fail_of_harmless hfail trivial
  · rintro ⟨g', h⟩
    simp only [analyze, Option.bind_eq_some_iff] at h
    obtain ⟨ga, ha, hb⟩ := h
    simp only [Option.some.injEq] at ha
    subst ha
    rw [if_neg (by simp)] at hb
    exact absurd hb (by simp)

end Structured
end Isolation
end PCA

import Mathlib
import RequestProject.NoCleanProvedWithEscape

/-!
# The isolation engine over `Finset` capability sets (Mathlib development)

This is a Mathlib-based rendering of the isolation-engine model of
`RequestProject.NoCleanProvedWithEscape`, where the capability sets held by the sandbox and by
the running application are `Finset Cap` rather than lists.

The same soundness/completeness package is proved here (`checkF_eq_true_iff_derivationF`,
`soundF`, `completeF`, `cleanF_iff_no_escapeF`, and the target-shaped
`no_clean_proved_with_escapeF`), and the two developments are connected by the bridge lemmas
`checkF_toFinset`, `cleanF_toFinset_iff`, and `escapesF_toFinset_iff`: on capability sets
presented as lists, the `Finset` engine and the core engine accept and escape on exactly the
same applications.
-/

namespace PCA
namespace Isolation
namespace WithFinset

/-- The result of running an application, with `Finset` capability sets. -/
inductive OutcomeF : Type
  /-- Terminated inside the sandbox holding capabilities `g`. -/
  | ok (g : Finset Cap) : OutcomeF
  /-- Escaped the sandbox at capability `c`. -/
  | escape (c : Cap) : OutcomeF
  deriving DecidableEq

/-- The runtime monitor over `Finset` capability sets. -/
def runF (policy : Finset Cap) : Finset Cap → Prog → OutcomeF
  | g, [] => OutcomeF.ok g
  | g, Instr.use c :: p => if c ∈ g then runF policy g p else OutcomeF.escape c
  | g, Instr.grant c :: p => if c ∈ policy then runF policy (insert c g) p else OutcomeF.escape c

/-- The static verifier over `Finset` capability sets. -/
def checkF (policy : Finset Cap) : Finset Cap → Prog → Bool
  | _, [] => true
  | g, Instr.use c :: p => if c ∈ g then checkF policy g p else false
  | g, Instr.grant c :: p => if c ∈ policy then checkF policy (insert c g) p else false

/-- The certificate logic over `Finset` capability sets. -/
inductive DerivationF (policy : Finset Cap) : Finset Cap → Prog → Prop
  | nil {g : Finset Cap} : DerivationF policy g []
  | use {g : Finset Cap} {c : Cap} {p : Prog} :
      c ∈ g → DerivationF policy g p → DerivationF policy g (Instr.use c :: p)
  | grant {g : Finset Cap} {c : Cap} {p : Prog} :
      c ∈ policy → DerivationF policy (insert c g) p → DerivationF policy g (Instr.grant c :: p)

/-- An application escapes the `Finset` sandbox. -/
def EscapesF (policy g : Finset Cap) (p : Prog) : Prop :=
  ∃ c : Cap, runF policy g p = OutcomeF.escape c

/-- An application is accepted by the `Finset` verifier. -/
def CleanF (policy g : Finset Cap) (p : Prog) : Prop :=
  checkF policy g p = true

/-- An application carries a `Finset`-model certificate. -/
def ProvedF (policy g : Finset Cap) (p : Prog) : Prop :=
  Nonempty (DerivationF policy g p)

/-! ### The verifier decides the certificate logic -/

theorem derivationF_of_checkF {policy : Finset Cap} :
    ∀ (g : Finset Cap) (p : Prog), checkF policy g p = true → DerivationF policy g p
  | _, [], _ => DerivationF.nil
  | g, Instr.use c :: p, h => by
      by_cases hc : c ∈ g
      · simp only [checkF, if_pos hc] at h
        exact DerivationF.use hc (derivationF_of_checkF g p h)
      · simp [checkF, hc] at h
  | g, Instr.grant c :: p, h => by
      by_cases hc : c ∈ policy
      · simp only [checkF, if_pos hc] at h
        exact DerivationF.grant hc (derivationF_of_checkF (insert c g) p h)
      · simp [checkF, hc] at h

theorem checkF_of_derivationF {policy : Finset Cap} {g : Finset Cap} {p : Prog}
    (d : DerivationF policy g p) : checkF policy g p = true := by
  induction d with
  | nil => rfl
  | use hc _ ih => simp [checkF, hc, ih]
  | grant hc _ ih => simp [checkF, hc, ih]

theorem checkF_eq_true_iff_derivationF {policy g : Finset Cap} {p : Prog} :
    checkF policy g p = true ↔ Nonempty (DerivationF policy g p) :=
  ⟨fun h => ⟨derivationF_of_checkF g p h⟩, fun ⟨d⟩ => checkF_of_derivationF d⟩

theorem cleanF_iff_provedF {policy g : Finset Cap} {p : Prog} :
    CleanF policy g p ↔ ProvedF policy g p :=
  checkF_eq_true_iff_derivationF

/-! ### Soundness and completeness -/

theorem runF_ok_of_checkF {policy : Finset Cap} :
    ∀ (g : Finset Cap) (p : Prog), checkF policy g p = true →
      ∃ g' : Finset Cap, runF policy g p = OutcomeF.ok g'
  | g, [], _ => ⟨g, rfl⟩
  | g, Instr.use c :: p, h => by
      by_cases hc : c ∈ g
      · simp only [checkF, if_pos hc] at h
        simpa [runF, hc] using runF_ok_of_checkF g p h
      · simp [checkF, hc] at h
  | g, Instr.grant c :: p, h => by
      by_cases hc : c ∈ policy
      · simp only [checkF, if_pos hc] at h
        simpa [runF, hc] using runF_ok_of_checkF (insert c g) p h
      · simp [checkF, hc] at h

/-- **Soundness** for the `Finset` model. -/
theorem soundF {policy g : Finset Cap} {p : Prog} (hclean : CleanF policy g p) :
    ¬ EscapesF policy g p := by
  rintro ⟨c, hc⟩
  obtain ⟨g', hg'⟩ := runF_ok_of_checkF g p hclean
  rw [hg'] at hc
  exact OutcomeF.noConfusion hc

theorem escapeF_of_not_checkF {policy : Finset Cap} :
    ∀ (g : Finset Cap) (p : Prog), checkF policy g p = false →
      ∃ c : Cap, runF policy g p = OutcomeF.escape c
  | _, [], h => by simp [checkF] at h
  | g, Instr.use c :: p, h => by
      by_cases hc : c ∈ g
      · simp only [checkF, if_pos hc] at h
        simpa [runF, hc] using escapeF_of_not_checkF g p h
      · exact ⟨c, by simp [runF, hc]⟩
  | g, Instr.grant c :: p, h => by
      by_cases hc : c ∈ policy
      · simp only [checkF, if_pos hc] at h
        simpa [runF, hc] using escapeF_of_not_checkF (insert c g) p h
      · exact ⟨c, by simp [runF, hc]⟩

/-- **Completeness** for the `Finset` model. -/
theorem completeF {policy g : Finset Cap} {p : Prog} (hsafe : ¬ EscapesF policy g p) :
    CleanF policy g p := by
  cases h : checkF policy g p with
  | true => exact h
  | false => exact absurd (escapeF_of_not_checkF g p h) hsafe

theorem cleanF_iff_no_escapeF {policy g : Finset Cap} {p : Prog} :
    CleanF policy g p ↔ ¬ EscapesF policy g p :=
  ⟨soundF, completeF⟩

/-- The target theorem in the `Finset` model: no application is at once clean, proved and
escaping. -/
theorem no_clean_proved_with_escapeF (policy g : Finset Cap) (p : Prog) :
    ¬ (CleanF policy g p ∧ ProvedF policy g p ∧ EscapesF policy g p) := by
  rintro ⟨hclean, -, hesc⟩
  exact soundF hclean hesc

/-! ### Bridge to the core (list-based) development -/

/-- The `Finset` verifier and the core verifier agree on capability sets given by lists. -/
theorem checkF_toFinset (policy : List Cap) :
    ∀ (g : List Cap) (p : Prog), checkF policy.toFinset g.toFinset p = check policy g p
  | _, [] => rfl
  | g, Instr.use c :: p => by
      by_cases hc : c ∈ g
      · simp only [checkF, check, if_pos hc, if_pos (List.mem_toFinset.mpr hc)]
        exact checkF_toFinset policy g p
      · simp [checkF, check, hc]
  | g, Instr.grant c :: p => by
      by_cases hc : c ∈ policy
      · have hins : insert c g.toFinset = (c :: g).toFinset := by
          simp [List.toFinset_cons]
        simp only [checkF, check, if_pos hc, if_pos (List.mem_toFinset.mpr hc), hins]
        exact checkF_toFinset policy (c :: g) p
      · simp [checkF, check, hc]

theorem cleanF_toFinset_iff {policy g : List Cap} {p : Prog} :
    CleanF policy.toFinset g.toFinset p ↔ Clean policy g p := by
  unfold CleanF Clean
  rw [checkF_toFinset]

/-- The two runtime monitors escape on exactly the same applications. -/
theorem escapesF_toFinset_iff {policy g : List Cap} {p : Prog} :
    EscapesF policy.toFinset g.toFinset p ↔ Escapes policy g p := by
  rw [← not_iff_not, ← cleanF_iff_no_escapeF, ← clean_iff_no_escape, cleanF_toFinset_iff]

/-- The core target theorem, re-derived from the `Finset` development through the bridge. -/
theorem no_clean_proved_with_escape_via_finset (policy g : List Cap) (p : Prog) :
    ¬ (Clean policy g p ∧ Proved policy g p ∧ Escapes policy g p) := by
  rintro ⟨hclean, -, hesc⟩
  exact no_clean_proved_with_escapeF policy.toFinset g.toFinset p
    ⟨cleanF_toFinset_iff.mpr hclean,
      cleanF_iff_provedF.mp (cleanF_toFinset_iff.mpr hclean),
      escapesF_toFinset_iff.mpr hesc⟩

end WithFinset
end Isolation
end PCA

/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (Lean 4 core only, no `import` line), so that the
required header comment can literally be the first thing in the file: Lean requires all
`import` commands to precede every other command, including module doc comments.

## The model

We model the isolation engine of a proof-carrying application platform.

* A *capability* is a natural number (an abstract name for a resource / syscall class).
* A *policy* is the list of capabilities the sandbox is willing to hand out.
* An *application* is a straight-line program: a list of instructions, each of which either
  *uses* a capability (performs an effect) or *grants* itself a capability.
* The *runtime monitor* (`run`) executes the program from a set of initially granted
  capabilities. A `use c` with `c` not currently granted, or a `grant c` with `c` outside the
  policy, is an **escape**: the sandbox boundary was crossed.
* The *static verifier* (`check`) is the boolean analysis the platform runs before admitting
  an app; an app is **clean** when the verifier accepts it.
* A *certificate* is a derivation in the proof system `Derivation`; an app is **proved** when
  such a certificate exists. This is the "proof" carried by a proof-carrying app.

The results below are the soundness/completeness package for this model:

* `check_eq_true_iff_derivation` : clean ↔ proved (the checker is a decision procedure for the
  certificate logic);
* `sound` : clean → no escape;
* `complete` : no escape → clean;
* `no_clean_proved_with_escape` : the target — no application is simultaneously clean, proved,
  and escaping.

A small-step semantics (`StepR`, `Steps`, `Stuck`) is also given, together with
`run_ok_iff_steps` and `escapes_iff_reachable_stuck`, showing that the big-step monitor agrees
with it and that `Escapes` is exactly reachability of a stuck (boundary-crossing)
configuration.
-/

namespace PCA
namespace Isolation

/-- A capability name. -/
abbrev Cap : Type := Nat

/-- Instructions of a sandboxed application. -/
inductive Instr : Type
  /-- Perform an effect requiring capability `c`. -/
  | use (c : Cap) : Instr
  /-- Acquire capability `c` from the sandbox. -/
  | grant (c : Cap) : Instr
  deriving DecidableEq, Repr

/-- An application is a straight-line program. -/
abbrev Prog : Type := List Instr

/-- The result of running an application under the runtime monitor. -/
inductive Outcome : Type
  /-- The program terminated inside the sandbox, holding capabilities `g`. -/
  | ok (g : List Cap) : Outcome
  /-- The program escaped the sandbox while trying to use/acquire capability `c`. -/
  | escape (c : Cap) : Outcome
  deriving DecidableEq, Repr

/-- The runtime monitor: execute `p` with policy `policy` from granted capabilities `g`. -/
def run (policy : List Cap) : List Cap → Prog → Outcome
  | g, [] => Outcome.ok g
  | g, Instr.use c :: p => if c ∈ g then run policy g p else Outcome.escape c
  | g, Instr.grant c :: p => if c ∈ policy then run policy (c :: g) p else Outcome.escape c

/-- The static verifier of the isolation engine. -/
def check (policy : List Cap) : List Cap → Prog → Bool
  | _, [] => true
  | g, Instr.use c :: p => if c ∈ g then check policy g p else false
  | g, Instr.grant c :: p => if c ∈ policy then check policy (c :: g) p else false

/-- The certificate logic carried by a proof-carrying app. -/
inductive Derivation (policy : List Cap) : List Cap → Prog → Prop
  /-- The empty program is trivially safe. -/
  | nil {g : List Cap} : Derivation policy g []
  /-- A use of a granted capability is safe if the continuation is. -/
  | use {g : List Cap} {c : Cap} {p : Prog} :
      c ∈ g → Derivation policy g p → Derivation policy g (Instr.use c :: p)
  /-- Acquiring a policy-permitted capability is safe if the continuation is. -/
  | grant {g : List Cap} {c : Cap} {p : Prog} :
      c ∈ policy → Derivation policy (c :: g) p → Derivation policy g (Instr.grant c :: p)

/-- An application *escapes* when the runtime monitor reports an escape. -/
def Escapes (policy : List Cap) (g : List Cap) (p : Prog) : Prop :=
  ∃ c : Cap, run policy g p = Outcome.escape c

/-- An application is *clean* when the static verifier accepts it. -/
def Clean (policy : List Cap) (g : List Cap) (p : Prog) : Prop :=
  check policy g p = true

/-- An application is *proved* when it carries a certificate. -/
def Proved (policy : List Cap) (g : List Cap) (p : Prog) : Prop :=
  Nonempty (Derivation policy g p)

/-! ### The verifier decides the certificate logic -/

theorem derivation_of_check {policy : List Cap} :
    ∀ (g : List Cap) (p : Prog), check policy g p = true → Derivation policy g p
  | _, [], _ => Derivation.nil
  | g, Instr.use c :: p, h => by
      by_cases hc : c ∈ g
      · simp only [check, if_pos hc] at h
        exact Derivation.use hc (derivation_of_check g p h)
      · simp [check, hc] at h
  | g, Instr.grant c :: p, h => by
      by_cases hc : c ∈ policy
      · simp only [check, if_pos hc] at h
        exact Derivation.grant hc (derivation_of_check (c :: g) p h)
      · simp [check, hc] at h

theorem check_of_derivation {policy : List Cap} {g : List Cap} {p : Prog}
    (d : Derivation policy g p) : check policy g p = true := by
  induction d with
  | nil => rfl
  | use hc _ ih => simp [check, hc, ih]
  | grant hc _ ih => simp [check, hc, ih]

/-- The static verifier is exactly a decision procedure for the certificate logic:
an application is clean iff it is proved. -/
theorem check_eq_true_iff_derivation {policy : List Cap} {g : List Cap} {p : Prog} :
    check policy g p = true ↔ Nonempty (Derivation policy g p) :=
  ⟨fun h => ⟨derivation_of_check g p h⟩, fun ⟨d⟩ => check_of_derivation d⟩

theorem clean_iff_proved {policy : List Cap} {g : List Cap} {p : Prog} :
    Clean policy g p ↔ Proved policy g p :=
  check_eq_true_iff_derivation

/-! ### Soundness and completeness of the verifier w.r.t. the runtime monitor -/

/-- If the verifier accepts, the run terminates inside the sandbox. -/
theorem run_ok_of_check {policy : List Cap} :
    ∀ (g : List Cap) (p : Prog), check policy g p = true → ∃ g' : List Cap, run policy g p = Outcome.ok g'
  | g, [], _ => ⟨g, rfl⟩
  | g, Instr.use c :: p, h => by
      by_cases hc : c ∈ g
      · simp only [check, if_pos hc] at h
        simpa [run, hc] using run_ok_of_check g p h
      · simp [check, hc] at h
  | g, Instr.grant c :: p, h => by
      by_cases hc : c ∈ policy
      · simp only [check, if_pos hc] at h
        simpa [run, hc] using run_ok_of_check (c :: g) p h
      · simp [check, hc] at h

/-- **Soundness**: a clean application never escapes the sandbox. -/
theorem sound {policy : List Cap} {g : List Cap} {p : Prog}
    (hclean : Clean policy g p) : ¬ Escapes policy g p := by
  rintro ⟨c, hc⟩
  obtain ⟨g', hg'⟩ := run_ok_of_check g p hclean
  rw [hg'] at hc
  exact Outcome.noConfusion hc

/-- If the verifier rejects, the runtime monitor observes an escape. -/
theorem escape_of_not_check {policy : List Cap} :
    ∀ (g : List Cap) (p : Prog), check policy g p = false → ∃ c : Cap, run policy g p = Outcome.escape c
  | _, [], h => by simp [check] at h
  | g, Instr.use c :: p, h => by
      by_cases hc : c ∈ g
      · simp only [check, if_pos hc] at h
        simpa [run, hc] using escape_of_not_check g p h
      · exact ⟨c, by simp [run, hc]⟩
  | g, Instr.grant c :: p, h => by
      by_cases hc : c ∈ policy
      · simp only [check, if_pos hc] at h
        simpa [run, hc] using escape_of_not_check (c :: g) p h
      · exact ⟨c, by simp [run, hc]⟩

/-- **Completeness**: an application that never escapes is accepted by the verifier. -/
theorem complete {policy : List Cap} {g : List Cap} {p : Prog}
    (hsafe : ¬ Escapes policy g p) : Clean policy g p := by
  cases h : check policy g p with
  | true => exact h
  | false => exact absurd (escape_of_not_check g p h) hsafe

/-- The isolation engine is exactly right: clean ↔ proved ↔ escape-free. -/
theorem clean_iff_no_escape {policy : List Cap} {g : List Cap} {p : Prog} :
    Clean policy g p ↔ ¬ Escapes policy g p :=
  ⟨sound, complete⟩

/-! ### The target theorem -/

/-- **No clean proved application escapes.** For every policy, every set of initially granted
capabilities and every application, it is impossible for the application to be simultaneously
accepted by the static verifier (`Clean`), accompanied by a valid certificate (`Proved`), and
still escape the sandbox at runtime (`Escapes`). -/
theorem no_clean_proved_with_escape (policy : List Cap) (g : List Cap) (p : Prog) :
    ¬ (Clean policy g p ∧ Proved policy g p ∧ Escapes policy g p) := by
  rintro ⟨hclean, -, hesc⟩
  exact sound hclean hesc

/-! ### Small-step operational semantics

The monitor `run` is a big-step description of execution. Here we give the corresponding
small-step semantics and show the two agree, so that `Escapes` really is the statement that
the sandboxed machine can get *stuck outside the sandbox*, rather than an artefact of how
`run` was written. -/

/-- A machine configuration: the capabilities currently held, and the remaining program. -/
abbrev Config : Type := List Cap × Prog

/-- One step of the sandboxed machine. Note there is *no* step out of a configuration whose
next instruction violates the sandbox: such configurations are stuck. -/
inductive StepR (policy : List Cap) : Config → Config → Prop
  /-- Using a currently granted capability. -/
  | use {g : List Cap} {c : Cap} {p : Prog} :
      c ∈ g → StepR policy (g, Instr.use c :: p) (g, p)
  /-- Acquiring a capability the policy permits. -/
  | grant {g : List Cap} {c : Cap} {p : Prog} :
      c ∈ policy → StepR policy (g, Instr.grant c :: p) (c :: g, p)

/-- Reflexive-transitive closure of `StepR`. -/
inductive Steps (policy : List Cap) : Config → Config → Prop
  | refl {a : Config} : Steps policy a a
  | head {a b c : Config} : StepR policy a b → Steps policy b c → Steps policy a c

/-- A configuration is *stuck* when the program has not finished yet no step is possible:
the machine is about to cross the sandbox boundary. -/
def Stuck (policy : List Cap) (cfg : Config) : Prop :=
  cfg.2 ≠ [] ∧ ∀ cfg' : Config, ¬ StepR policy cfg cfg'

theorem run_eq_of_step {policy : List Cap} {a b : Config} (h : StepR policy a b) :
    run policy a.1 a.2 = run policy b.1 b.2 := by
  cases h with
  | use hc => simp [run, hc]
  | grant hc => simp [run, hc]

theorem run_eq_of_steps {policy : List Cap} {a b : Config} (h : Steps policy a b) :
    run policy a.1 a.2 = run policy b.1 b.2 := by
  induction h with
  | refl => rfl
  | head hstep _ ih => exact (run_eq_of_step hstep).trans ih

theorem steps_of_run_ok {policy : List Cap} :
    ∀ (g : List Cap) (p : Prog) (g' : List Cap),
      run policy g p = Outcome.ok g' → Steps policy (g, p) (g', [])
  | g, [], g', h => by
      have hg : g = g' := by injection h
      subst hg
      exact Steps.refl
  | g, Instr.use c :: p, g', h => by
      by_cases hc : c ∈ g
      · simp only [run, if_pos hc] at h
        exact Steps.head (StepR.use hc) (steps_of_run_ok g p g' h)
      · simp [run, hc] at h
  | g, Instr.grant c :: p, g', h => by
      by_cases hc : c ∈ policy
      · simp only [run, if_pos hc] at h
        exact Steps.head (StepR.grant hc) (steps_of_run_ok (c :: g) p g' h)
      · simp [run, hc] at h

/-- Big-step and small-step semantics agree on successful runs. -/
theorem run_ok_iff_steps {policy : List Cap} {g g' : List Cap} {p : Prog} :
    run policy g p = Outcome.ok g' ↔ Steps policy (g, p) (g', []) := by
  refine ⟨steps_of_run_ok g p g', fun h => ?_⟩
  simpa [run] using run_eq_of_steps h

theorem escape_of_stuck {policy : List Cap} :
    ∀ cfg : Config, Stuck policy cfg → ∃ c : Cap, run policy cfg.1 cfg.2 = Outcome.escape c
  | (_, []), h => absurd rfl h.1
  | (g, Instr.use c :: p), h => by
      by_cases hc : c ∈ g
      · exact absurd (StepR.use (p := p) hc) (h.2 (g, p))
      · exact ⟨c, by simp [run, hc]⟩
  | (g, Instr.grant c :: p), h => by
      by_cases hc : c ∈ policy
      · exact absurd (StepR.grant (g := g) (p := p) hc) (h.2 (c :: g, p))
      · exact ⟨c, by simp [run, hc]⟩

theorem reachable_stuck_of_escape {policy : List Cap} :
    ∀ (g : List Cap) (p : Prog) (c : Cap), run policy g p = Outcome.escape c →
      ∃ cfg : Config, Steps policy (g, p) cfg ∧ Stuck policy cfg
  | _, [], _, h => by simp [run] at h
  | g, Instr.use c :: p, d, h => by
      by_cases hc : c ∈ g
      · simp only [run, if_pos hc] at h
        obtain ⟨cfg, hsteps, hstuck⟩ := reachable_stuck_of_escape g p d h
        exact ⟨cfg, Steps.head (StepR.use hc) hsteps, hstuck⟩
      · refine ⟨(g, Instr.use c :: p), Steps.refl, by simp, ?_⟩
        rintro cfg' hstep
        cases hstep with
        | use hmem => exact hc hmem
  | g, Instr.grant c :: p, d, h => by
      by_cases hc : c ∈ policy
      · simp only [run, if_pos hc] at h
        obtain ⟨cfg, hsteps, hstuck⟩ := reachable_stuck_of_escape (c :: g) p d h
        exact ⟨cfg, Steps.head (StepR.grant hc) hsteps, hstuck⟩
      · refine ⟨(g, Instr.grant c :: p), Steps.refl, by simp, ?_⟩
        rintro cfg' hstep
        cases hstep with
        | grant hmem => exact hc hmem

/-- An application escapes exactly when the small-step machine can reach a stuck
configuration: `Escapes` is a genuine reachability property of the sandbox semantics. -/
theorem escapes_iff_reachable_stuck {policy : List Cap} {g : List Cap} {p : Prog} :
    Escapes policy g p ↔ ∃ cfg : Config, Steps policy (g, p) cfg ∧ Stuck policy cfg := by
  constructor
  · rintro ⟨c, hc⟩
    exact reachable_stuck_of_escape g p c hc
  · rintro ⟨cfg, hsteps, hstuck⟩
    obtain ⟨c, hc⟩ := escape_of_stuck cfg hstuck
    exact ⟨c, (run_eq_of_steps hsteps).trans hc⟩

/-- Restated soundness against the small-step semantics: a clean, certified application can
never reach a stuck (boundary-crossing) configuration. -/
theorem no_reachable_stuck_of_clean {policy : List Cap} {g : List Cap} {p : Prog}
    (hclean : Clean policy g p) :
    ¬ ∃ cfg : Config, Steps policy (g, p) cfg ∧ Stuck policy cfg :=
  fun h => sound hclean (escapes_iff_reachable_stuck.mpr h)

/-! ### Sanity checks: the model is not vacuous -/

/-- An application that escapes: it uses a capability it was never granted. -/
example : Escapes [1] [] [Instr.use 0] := ⟨0, rfl⟩

/-- That application is neither clean nor proved. -/
example : ¬ Clean [1] [] [Instr.use 0] := fun h => Bool.noConfusion h

/-- An application that acquires a permitted capability and then uses it is clean, proved,
and escape-free. -/
example : Clean [1] [] [Instr.grant 1, Instr.use 1] := rfl

example : Proved [1] [] [Instr.grant 1, Instr.use 1] :=
  clean_iff_proved.mp rfl

example : ¬ Escapes [1] [] [Instr.grant 1, Instr.use 1] :=
  sound rfl

/-- Granting a capability outside the policy is an escape. -/
example : Escapes [1] [] [Instr.grant 2] := ⟨2, rfl⟩

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

