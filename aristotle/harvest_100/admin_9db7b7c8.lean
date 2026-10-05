import Mathlib
import RequestProject.PCA.Invariant

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

#print axioms PCA.Invariant.rls_off_implies_no_row_protection

/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA
namespace Invariant

universe u v

/-- A row-level security policy on a table: a permissive predicate saying which
subjects may see which rows. -/
structure Policy (Subject : Type u) (Row : Type v) where
  /-- `applies s r` holds when the policy grants subject `s` access to row `r`. -/
  applies : Subject → Row → Prop

/-- A table of the isolation engine's model: a membership predicate describing the
stored rows, a row-level-security switch, and a list of permissive policies which is
consulted only when the switch is on. -/
structure Table (Subject : Type u) (Row : Type v) where
  /-- `rows r` holds when `r` is stored in the table. -/
  rows : Row → Prop
  /-- Whether row-level security is enabled for this table. -/
  rlsEnabled : Bool
  /-- The permissive policies attached to the table. -/
  policies : List (Policy Subject Row)

variable {Subject : Type u} {Row : Type v}

/-- The engine's access decision: a row is visible to a subject when it is stored in
the table and, *if* row-level security is enabled, some permissive policy grants
access. With RLS off the policy list is never consulted. -/
def Visible (t : Table Subject Row) (s : Subject) (r : Row) : Prop :=
  t.rows r ∧ (t.rlsEnabled = true → ∃ p ∈ t.policies, p.applies s r)

/-- A row enjoys *row protection* when it is stored in the table yet is hidden from
at least one subject. -/
def RowProtected (t : Table Subject Row) (r : Row) : Prop :=
  t.rows r ∧ ∃ s : Subject, ¬ Visible t s r

/-- With row-level security disabled, every stored row is visible to every subject. -/
theorem visible_of_rls_off {t : Table Subject Row} (h : t.rlsEnabled = false)
    (s : Subject) {r : Row} (hr : t.rows r) : Visible t s r := by
  refine ⟨hr, fun hon => ?_⟩
  rw [h] at hon
  exact Bool.noConfusion hon

/-- **Main invariant.** If row-level security is off for a table, then no row of that
table is protected: the isolation engine provides no row-level protection at all. -/
theorem rls_off_implies_no_row_protection {t : Table Subject Row}
    (h : t.rlsEnabled = false) : ∀ r : Row, ¬ RowProtected t r := by
  rintro r ⟨hr, s, hs⟩
  exact hs (visible_of_rls_off h s hr)

/-- Sanity check that the model is not degenerate: with row-level security *on* and
no policies attached, a stored row *is* protected (given at least one subject). -/
theorem rowProtected_of_rls_on_no_policies {t : Table Subject Row}
    (hon : t.rlsEnabled = true) (hp : t.policies = []) (s : Subject) {r : Row}
    (hr : t.rows r) : RowProtected t r := by
  refine ⟨hr, s, fun hv => ?_⟩
  obtain ⟨p, hpmem, -⟩ := hv.2 hon
  rw [hp] at hpmem
  exact List.not_mem_nil hpmem

end Invariant
end PCA

