/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires `import` commands to precede every other
command in a file, including module docstrings.  Since the mandated header
above must be the very first text in the file, this development is written so
that it needs nothing beyond Lean's built-in `Init` library (the prefix API on
lists), and therefore has no `import` line.  The Mathlib-based project settings
of the original template are not needed here.
-/

set_option autoImplicit false

namespace PCA
namespace Isolation

/-- A resource name in the isolation engine's model: a hierarchical path,
given as the list of its segments (e.g. `["home", "user", "docs"]`). -/
abbrev Path : Type := List String

/-- A *scope* of an isolated component: a list of permitted roots (`allow`)
together with a list of forbidden roots (`deny`).  A resource is governed by a
root exactly when the root is a path-prefix of the resource, and denial takes
precedence over permission. -/
structure Scope where
  /-- Roots under which access is granted. -/
  allow : List Path
  /-- Roots under which access is revoked, overriding `allow`. -/
  deny : List Path
  deriving Repr

/-- The declarative (specification-level) meaning of "resource `r` lies in scope `s`":
some allowed root governs `r`, and no denied root governs `r`. -/
def InScope (s : Scope) (r : Path) : Prop :=
  (∃ a ∈ s.allow, a <+: r) ∧ ∀ d ∈ s.deny, ¬ (d <+: r)

/-- The operational encoding used by the isolation engine: a purely Boolean
decision procedure over the scope's root lists. -/
def encodeInScope (s : Scope) (r : Path) : Bool :=
  s.allow.any (fun a => a.isPrefixOf r) && s.deny.all (fun d => !(d.isPrefixOf r))

/-- The Boolean prefix test agrees with the propositional prefix relation on paths. -/
theorem isPrefixOf_eq_true_iff (a r : Path) : a.isPrefixOf r = true ↔ a <+: r :=
  List.isPrefixOf_iff_prefix

/-- Failure of the Boolean prefix test means the prefix relation genuinely fails. -/
theorem isPrefixOf_eq_false_iff (a r : Path) : a.isPrefixOf r = false ↔ ¬ a <+: r := by
  rw [← isPrefixOf_eq_true_iff, Bool.not_eq_true]

/-- **Soundness and completeness of the in-scope encoding.**
The isolation engine's Boolean decision procedure `encodeInScope` accepts a
resource exactly when the resource genuinely lies in the declared scope. -/
theorem in_scope_encoding_sound (s : Scope) (r : Path) :
    encodeInScope s r = true ↔ InScope s r := by
  unfold encodeInScope InScope
  simp [List.any_eq_true, List.all_eq_true, isPrefixOf_eq_false_iff]

/-- Soundness direction: acceptance implies the resource really is in scope. -/
theorem in_scope_encoding_sound_forward (s : Scope) (r : Path)
    (h : encodeInScope s r = true) : InScope s r :=
  (in_scope_encoding_sound s r).mp h

/-- Completeness direction: an in-scope resource is accepted. -/
theorem in_scope_encoding_complete (s : Scope) (r : Path)
    (h : InScope s r) : encodeInScope s r = true :=
  (in_scope_encoding_sound s r).mpr h

/-- Contrapositive form: rejection means the resource is genuinely out of scope. -/
theorem not_in_scope_of_encoding_false (s : Scope) (r : Path)
    (h : encodeInScope s r = false) : ¬ InScope s r := by
  intro hs
  rw [in_scope_encoding_complete s r hs] at h
  exact Bool.noConfusion h

/-- Denial has absolute priority: a resource governed by a denied root is never
in scope, whatever the `allow` list says. -/
theorem not_in_scope_of_denied (s : Scope) (r : Path) {d : Path}
    (hd : d ∈ s.deny) (hpre : d <+: r) : ¬ InScope s r := fun h => h.2 d hd hpre

/-- The empty scope isolates completely: no resource is accessible. -/
theorem not_in_scope_empty (r : Path) : ¬ InScope ⟨[], []⟩ r := by
  rintro ⟨⟨a, ha, -⟩, -⟩
  exact absurd ha List.not_mem_nil

end Isolation
end PCA

