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

/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Coverage

universe u v

/-- A single handling *rule* of the isolation engine: a decidable guard saying which
inputs the rule recognizes, together with the action it performs on such inputs. -/
structure Rule (Input : Type u) (Output : Type v) where
  /-- The guard: `guard i = true` means this rule recognizes the input `i`. -/
  guard : Input → Bool
  /-- The action performed on a recognized input. -/
  action : Input → Output

variable {Input : Type u} {Output : Type v}

/-- A rule is *sound* for a specification `spec` when, on every input it recognizes,
its action satisfies the specification. Nothing at all is required of the action off
the guard — that is the point of isolating unrecognized inputs. -/
def Rule.Sound (spec : Input → Output → Prop) (r : Rule Input Output) : Prop :=
  ∀ i, r.guard i = true → spec i (r.action i)

/-- The isolation engine: try the rules in order; the first rule whose guard fires
handles the input. If no rule recognizes the input, the engine *bails* (`none`). -/
def dispatch (rs : List (Rule Input Output)) (i : Input) : Option Output :=
  match rs with
  | [] => none
  | r :: rest => if r.guard i then some (r.action i) else dispatch rest i

@[simp] theorem dispatch_nil (i : Input) : dispatch ([] : List (Rule Input Output)) i = none :=
  rfl

theorem dispatch_cons (r : Rule Input Output) (rs : List (Rule Input Output)) (i : Input) :
    dispatch (r :: rs) i = if r.guard i then some (r.action i) else dispatch rs i :=
  rfl

/-- An input is *covered* by the engine when at least one of its rules recognizes it. -/
def Covered (rs : List (Rule Input Output)) (i : Input) : Prop :=
  ∃ r, r ∈ rs ∧ r.guard i = true

/-!
## Main theorem
-/

/-- **Bail on unrecognized is sound.** If every rule of the isolation engine is sound
on the inputs it recognizes, then every output the engine actually produces satisfies
the specification. Inputs that no rule recognizes are bailed on (`none`), so no
unverified answer can escape. -/
theorem bail_on_unrecognized_is_sound
    (spec : Input → Output → Prop) (rs : List (Rule Input Output))
    (hrs : ∀ r ∈ rs, Rule.Sound spec r) :
    ∀ i o, dispatch rs i = some o → spec i o := by
  induction rs with
  | nil =>
      intro i o h
      exact absurd h (by simp)
  | cons r rest ih =>
      intro i o h
      rw [dispatch_cons] at h
      by_cases hg : r.guard i = true
      · rw [if_pos hg] at h
        have ho : o = r.action i := by
          have := Option.some.inj h
          exact this.symm
        subst ho
        exact hrs r (List.mem_cons_self ..) i hg
      · rw [if_neg hg] at h
        exact ih (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')) i o h

/-!
## The bail behaviour itself
-/

/-- The engine bails exactly on the inputs that no rule recognizes. -/
theorem dispatch_eq_none_iff (rs : List (Rule Input Output)) (i : Input) :
    dispatch rs i = none ↔ ¬ Covered rs i := by
  induction rs with
  | nil =>
      constructor
      · intro _ hc
        exact absurd hc.choose_spec.1 (by simp)
      · intro _
        rfl
  | cons r rest ih =>
      rw [dispatch_cons]
      by_cases hg : r.guard i = true
      · rw [if_pos hg]
        constructor
        · intro h
          exact absurd h (by simp)
        · intro h
          exact absurd ⟨r, List.mem_cons_self .., hg⟩ h
      · rw [if_neg hg]
        constructor
        · intro h hc
          have hnc : ¬ Covered rest i := ih.mp h
          match hc with
          | ⟨r', hmem, hg'⟩ =>
            match List.mem_cons.mp hmem with
            | Or.inl he => exact hg (he ▸ hg')
            | Or.inr hm => exact hnc ⟨r', hm, hg'⟩
        · intro h
          refine ih.mpr ?_
          intro hc
          match hc with
          | ⟨r', hmem, hg'⟩ => exact h ⟨r', List.mem_cons_of_mem _ hmem, hg'⟩

/-- Whenever the engine produces an answer, the input was covered: it never answers
on unrecognized input. -/
theorem covered_of_dispatch_eq_some
    (rs : List (Rule Input Output)) (i : Input) (o : Output)
    (h : dispatch rs i = some o) : Covered rs i := by
  by_cases hc : Covered rs i
  · exact hc
  · rw [(dispatch_eq_none_iff rs i).mpr hc] at h
    exact absurd h (by simp)

/-- Relative completeness: on every covered input the engine does answer. -/
theorem dispatch_isSome_of_covered
    (rs : List (Rule Input Output)) (i : Input) (h : Covered rs i) :
    (dispatch rs i).isSome = true := by
  cases hd : dispatch rs i with
  | none => exact absurd h ((dispatch_eq_none_iff rs i).mp hd)
  | some o => rfl

/-- Partial-correctness packaging of the isolation engine: any produced output meets
the specification, and the result is `none` on exactly the unrecognized inputs. -/
theorem dispatch_sound_and_bails
    (spec : Input → Output → Prop) (rs : List (Rule Input Output))
    (hrs : ∀ r ∈ rs, Rule.Sound spec r) (i : Input) :
    (∀ o, dispatch rs i = some o → spec i o) ∧ (dispatch rs i = none ↔ ¬ Covered rs i) :=
  ⟨bail_on_unrecognized_is_sound spec rs hrs i, dispatch_eq_none_iff rs i⟩

end PCA.Coverage

