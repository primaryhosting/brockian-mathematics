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

