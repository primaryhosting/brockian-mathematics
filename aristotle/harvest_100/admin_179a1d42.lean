/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 does not permit any command (including a module docstring) to precede
the `import` block, so in order for this file to *begin* with the header comment above it is
kept import-free.  Everything below is therefore developed from scratch on top of core Lean 4
(the file compiles unchanged inside this Mathlib project, and uses no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA
namespace Isolation

/-! ## The isolation engine's model

Privilege levels are natural numbers, higher meaning more privileged.  An app runs inside an
isolation boundary `bound : Nat` and holds a set `avail` of capabilities.  Exercising a
capability requires a privilege level and confers one. -/

/-- A set of capabilities, represented as a predicate on capability names. -/
def Caps : Type := Nat → Prop

/-- Membership of a capability in a capability set. -/
def Caps.mem (avail : Caps) (c : Nat) : Prop := avail c

instance : Membership Nat Caps := ⟨Caps.mem⟩

/-- Containment of capability sets. -/
def Caps.Subset (avail avail' : Caps) : Prop := ∀ c, c ∈ avail → c ∈ avail'

instance : HasSubset Caps := ⟨Caps.Subset⟩

/-- An isolation policy for a proof-carrying app.

`req c` is the privilege level required to exercise capability `c`, and `gain c` is the
privilege level that exercising `c` confers. -/
structure Policy where
  /-- Privilege required to exercise a capability. -/
  req : Nat → Nat
  /-- Privilege conferred by exercising a capability. -/
  gain : Nat → Nat

/-- One step of the isolation engine: from privilege `p`, an app holding some available
capability `c` whose requirement it meets may move to privilege `max p (gain c)`.
Privilege is never dropped by a step. -/
def Step (pol : Policy) (avail : Caps) (p q : Nat) : Prop :=
  ∃ c, c ∈ avail ∧ pol.req c ≤ p ∧ q = max p (pol.gain c)

/-- Reachability of privilege levels: the reflexive-transitive closure of `Step`. -/
inductive Reach (pol : Policy) (avail : Caps) : Nat → Nat → Prop
  | refl (p : Nat) : Reach pol avail p p
  | tail {p q r : Nat} : Reach pol avail p q → Step pol avail q r → Reach pol avail p r

/-- The app *escapes* the isolation boundary `bound` from privilege `p` when some privilege
level strictly above `bound` is reachable. -/
def Escapes (pol : Policy) (avail : Caps) (bound p : Nat) : Prop :=
  ∃ q, Reach pol avail p q ∧ bound < q

/-! ## Basic facts about steps and reachability -/

/-- A single step never lowers the privilege level. -/
theorem Step.le {pol : Policy} {avail : Caps} {p q : Nat} (h : Step pol avail p q) :
    p ≤ q := by
  obtain ⟨c, -, -, rfl⟩ := h
  omega

/-- Reachability never lowers the privilege level. -/
theorem Reach.le {pol : Policy} {avail : Caps} {p q : Nat} (h : Reach pol avail p q) :
    p ≤ q := by
  induction h with
  | refl => exact Nat.le_refl p
  | tail _ hstep ih => exact Nat.le_trans ih hstep.le

/-- A single step from `p` is realized as a single step of `Reach`. -/
theorem Reach.single {pol : Policy} {avail : Caps} {p q : Nat} (h : Step pol avail p q) :
    Reach pol avail p q :=
  Reach.tail (Reach.refl p) h

/-- **Step simulation.** A step available in a smaller capability set is available in a larger
one, and a larger starting privilege still permits it, reaching an at-least-as-large
privilege. -/
theorem Step.simulate {pol : Policy} {avail avail' : Caps} {p q p' : Nat}
    (h : Step pol avail p q) (hav : avail ⊆ avail') (hp : p ≤ p') :
    ∃ q', Step pol avail' p' q' ∧ q ≤ q' := by
  obtain ⟨c, hc, hreq, rfl⟩ := h
  exact ⟨max p' (pol.gain c), ⟨c, hav _ hc, Nat.le_trans hreq hp, rfl⟩, by omega⟩

/-- **Reachability simulation.** Raising the starting privilege and enlarging the set of
available capabilities can only reach higher privilege levels. -/
theorem Reach.simulate {pol : Policy} {avail avail' : Caps} {p q p' : Nat}
    (h : Reach pol avail p q) (hav : avail ⊆ avail') (hp : p ≤ p') :
    ∃ q', Reach pol avail' p' q' ∧ q ≤ q' := by
  induction h with
  | refl => exact ⟨p', Reach.refl p', hp⟩
  | tail _ hstep ih =>
      obtain ⟨b', hb', hbb'⟩ := ih
      obtain ⟨c', hstep', hcc'⟩ := hstep.simulate hav hbb'
      exact ⟨c', hb'.tail hstep', hcc'⟩

/-! ## The main monotonicity theorem -/

/-- **Privilege escape is monotone.**

If an app can escape the isolation boundary `bound` starting from privilege `p` using the
capabilities in `avail`, then it can also escape any tighter boundary `bound' ≤ bound`
starting from any higher privilege `p' ≥ p` with any larger capability set `avail' ⊇ avail`.

Equivalently: escape is upward closed in the attacker's starting resources and downward
closed in the strength of the isolation boundary.  Contrapositively, isolation proved for a
configuration transfers to every weaker attacker and every wider boundary. -/
theorem priv_escape_monotone {pol : Policy} {avail avail' : Caps} {bound bound' p p' : Nat}
    (hav : avail ⊆ avail') (hb : bound' ≤ bound) (hp : p ≤ p')
    (h : Escapes pol avail bound p) : Escapes pol avail' bound' p' := by
  obtain ⟨q, hreach, hq⟩ := h
  obtain ⟨q', hreach', hqq'⟩ := hreach.simulate hav hp
  exact ⟨q', hreach', by omega⟩

/-! ## Soundness and completeness of the isolation check

The engine certifies isolation at boundary `bound` by the purely local check

  `∀ c ∈ avail, req c ≤ bound → gain c ≤ bound`,

i.e. no available capability that can be exercised from inside the boundary confers privilege
outside it.  This check is both sound and complete for escape freedom. -/

/-- The isolation engine's local certificate check. -/
def Certified (pol : Policy) (avail : Caps) (bound : Nat) : Prop :=
  ∀ c, c ∈ avail → pol.req c ≤ bound → pol.gain c ≤ bound

/-- **Soundness (invariant form).** If the local check passes, then no privilege above the
boundary is reachable from any privilege inside the boundary. -/
theorem reach_le_of_certified {pol : Policy} {avail : Caps} {bound p q : Nat}
    (hcert : Certified pol avail bound) (hp : p ≤ bound) (h : Reach pol avail p q) :
    q ≤ bound := by
  induction h with
  | refl => exact hp
  | tail _ hstep ih =>
      obtain ⟨d, hd, hreq, rfl⟩ := hstep
      have := hcert d hd (Nat.le_trans hreq ih)
      omega

/-- **Soundness.** A certified configuration admits no privilege escape. -/
theorem not_escapes_of_certified {pol : Policy} {avail : Caps} {bound p : Nat}
    (hcert : Certified pol avail bound) (hp : p ≤ bound) :
    ¬ Escapes pol avail bound p := by
  rintro ⟨q, hreach, hq⟩
  have := reach_le_of_certified hcert hp hreach
  omega

/-- **Completeness.** If the local check fails, then an app starting at privilege exactly
`bound` — hence inside the boundary — really does escape. -/
theorem escapes_of_not_certified {pol : Policy} {avail : Caps} {bound : Nat}
    (hcert : ¬ Certified pol avail bound) :
    Escapes pol avail bound bound := by
  refine Classical.byContradiction (fun hesc => hcert ?_)
  intro c hc hreq
  refine Classical.byContradiction (fun hgain => hesc ?_)
  exact ⟨max bound (pol.gain c), Reach.single ⟨c, hc, hreq, rfl⟩, by omega⟩

/-- **Soundness and completeness of the isolation engine.**  The local certificate check
holds exactly when no app starting inside the isolation boundary can escape it. -/
theorem certified_iff_no_escape {pol : Policy} {avail : Caps} {bound : Nat} :
    Certified pol avail bound ↔ ∀ p, p ≤ bound → ¬ Escapes pol avail bound p := by
  constructor
  · intro hcert p hp
    exact not_escapes_of_certified hcert hp
  · intro h
    exact Classical.byContradiction fun hcert =>
      h bound (Nat.le_refl bound) (escapes_of_not_certified hcert)

/-- Escape freedom is antitone in the attacker's resources: the contrapositive form of
`priv_escape_monotone`, which is how the isolation engine reuses proofs. -/
theorem no_escape_antitone {pol : Policy} {avail avail' : Caps} {bound bound' p p' : Nat}
    (hav : avail ⊆ avail') (hb : bound' ≤ bound) (hp : p ≤ p')
    (h : ¬ Escapes pol avail' bound' p') : ¬ Escapes pol avail bound p :=
  fun hesc => h (priv_escape_monotone hav hb hp hesc)

/-! ## Non-vacuity checks

The model really does exhibit escapes, so the theorems above are not vacuous. -/

/-- A policy with one freely usable capability that confers privilege `5`. -/
def demoPolicy : Policy where
  req := fun _ => 0
  gain := fun _ => 5

/-- The capability set `{1}`. -/
def demoCaps : Caps := fun c => c = 1

/-- An unprivileged app with capability `1` escapes the boundary `3`. -/
example : Escapes demoPolicy demoCaps 3 0 :=
  ⟨max 0 (demoPolicy.gain 1), Reach.single ⟨1, rfl, Nat.le_refl 0, rfl⟩, by decide⟩

/-- Hence, by monotonicity, it escapes the tighter boundary `2` from privilege `4` with the
larger capability set of all capabilities. -/
example : Escapes demoPolicy (fun _ => True) 2 4 :=
  priv_escape_monotone (avail := demoCaps) (bound := 3) (p := 0)
    (fun _ _ => trivial) (by decide) (by decide)
    ⟨max 0 (demoPolicy.gain 1), Reach.single ⟨1, rfl, Nat.le_refl 0, rfl⟩, by decide⟩

/-- The same configuration is not certified at boundary `3`. -/
example : ¬ Certified demoPolicy demoCaps 3 := fun h => by
  have := h 1 rfl (by decide)
  simp only [demoPolicy] at this
  omega

/-- But it is certified — hence escape free — at boundary `5`. -/
example : Certified demoPolicy demoCaps 5 := fun _ _ _ => Nat.le_refl 5

#print axioms priv_escape_monotone
#print axioms certified_iff_no_escape
#print axioms not_escapes_of_certified
#print axioms escapes_of_not_certified

end Isolation
end PCA

