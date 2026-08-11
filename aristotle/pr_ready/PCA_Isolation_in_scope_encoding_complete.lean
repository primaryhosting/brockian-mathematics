/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace PCA.Isolation

/-- Tenants are identified by a natural number. -/
abbrev Tenant := ℕ

/-- Resource identifiers are natural numbers. -/
abbrev ResId := ℕ

/-- A resource is owned by a tenant and carries a resource identifier. -/
structure Resource where
  tenant : Tenant
  rid : ResId
deriving DecidableEq, Repr

/-- A scope is the authority of one tenant over a finite set of resource identifiers. -/
structure Scope where
  tenant : Tenant
  allowed : Finset ResId

/-- The ground-truth access predicate: `r` is visible in scope `s` when it belongs to the
scope's tenant and its identifier is explicitly allowed. -/
def InScope (s : Scope) (r : Resource) : Prop :=
  r.tenant = s.tenant ∧ r.rid ∈ s.allowed

instance (s : Scope) (r : Resource) : Decidable (InScope s r) := by
  unfold InScope; infer_instance

/-- The canonical (sorted, duplicate-free) enumeration of the identifiers of a scope. -/
def handles (s : Scope) : List ResId := s.allowed.sort (· ≤ ·)

lemma mem_handles {s : Scope} {x : ResId} : x ∈ handles s ↔ x ∈ s.allowed :=
  Finset.mem_sort _

lemma handles_nodup (s : Scope) : (handles s).Nodup :=
  Finset.sort_nodup _ _

lemma length_handles (s : Scope) : (handles s).length = s.allowed.card :=
  Finset.length_sort _

/-- The isolation engine: issue a dense handle for an in-scope resource, and refuse
(`none`) for everything else. -/
def encode (s : Scope) (r : Resource) : Option ℕ :=
  if InScope s r then some ((handles s).idxOf r.rid) else none

/-- Resolution of a handle back to a resource, within a scope. -/
def decode (s : Scope) (i : ℕ) : Option Resource :=
  ((handles s)[i]?).map fun rid => ⟨s.tenant, rid⟩

/-! ### Basic behaviour of `encode` -/

lemma encode_eq_none_iff {s : Scope} {r : Resource} :
    encode s r = none ↔ ¬ InScope s r := by
  unfold encode; split <;> simp_all

lemma encode_of_inScope {s : Scope} {r : Resource} (h : InScope s r) :
    encode s r = some ((handles s).idxOf r.rid) := by
  unfold encode; simp [h]

lemma idxOf_lt_card {s : Scope} {r : Resource} (h : InScope s r) :
    (handles s).idxOf r.rid < s.allowed.card := by
  rw [← length_handles]
  exact List.idxOf_lt_length_iff.2 (mem_handles.2 h.2)

/-- **Soundness of encoding.** A handle is only ever issued for an in-scope resource, and it
always lies in the dense range `[0, |scope|)`. -/
theorem encode_sound {s : Scope} {r : Resource} {i : ℕ} (h : encode s r = some i) :
    InScope s r ∧ i < s.allowed.card := by
  unfold encode at h
  split at h
  · rename_i hs
    exact ⟨hs, by simpa [Option.some_inj.1 h] using idxOf_lt_card hs⟩
  · simp at h

/-- **Cross-tenant isolation.** A resource belonging to another tenant is never encoded. -/
theorem cross_tenant_isolation {s : Scope} {r : Resource} (h : r.tenant ≠ s.tenant) :
    encode s r = none :=
  encode_eq_none_iff.2 fun hs => h hs.1

/-- **Soundness of decoding.** Any resource obtained by resolving a handle is in scope, and
its handle is the one it came from. -/
theorem decode_sound {s : Scope} {i : ℕ} {r : Resource} (h : decode s i = some r) :
    InScope s r ∧ encode s r = some i ∧ i < s.allowed.card := by
  unfold decode at h
  rcases Option.map_eq_some_iff.1 h with ⟨rid, hrid, hr⟩
  rcases List.getElem?_eq_some_iff.1 hrid with ⟨hlt, hget⟩
  subst hr
  have hmem : rid ∈ s.allowed := by
    rw [← mem_handles, ← hget]
    exact List.getElem_mem hlt
  have hscope : InScope s ⟨s.tenant, rid⟩ := ⟨rfl, hmem⟩
  refine ⟨hscope, ?_, by simpa [length_handles] using hlt⟩
  rw [encode_of_inScope hscope, ← hget, (handles_nodup s).idxOf_getElem]

/-- Resolving the handle of an in-scope resource returns exactly that resource. -/
theorem decode_encode {s : Scope} {r : Resource} (h : InScope s r) :
    decode s ((handles s).idxOf r.rid) = some r := by
  have hlt : (handles s).idxOf r.rid < (handles s).length :=
    List.idxOf_lt_length_iff.2 (mem_handles.2 h.2)
  unfold decode
  rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  cases r with
  | mk t rid =>
      have ht : t = s.tenant := h.1
      subst ht
      simp

/-- **Soundness and completeness of the isolation engine.**

A resource is in scope for `s` if and only if the engine issues a handle for it; moreover such
a handle is automatically dense (below the size of the scope) and resolves back to exactly the
resource it was issued for. -/
theorem in_scope_encoding_complete (s : Scope) (r : Resource) :
    InScope s r ↔ ∃ i, encode s r = some i ∧ i < s.allowed.card ∧ decode s i = some r := by
  constructor
  · intro h
    exact ⟨(handles s).idxOf r.rid, encode_of_inScope h, idxOf_lt_card h, decode_encode h⟩
  · rintro ⟨i, hi, -, -⟩
    exact (encode_sound hi).1

/-- Distinct in-scope resources are never confused by the engine. -/
theorem encode_injective_on_scope {s : Scope} {r₁ r₂ : Resource}
    (h₁ : InScope s r₁) (h₂ : InScope s r₂) (h : encode s r₁ = encode s r₂) : r₁ = r₂ := by
  have e₁ := decode_encode h₁
  have e₂ := decode_encode h₂
  rw [encode_of_inScope h₁, encode_of_inScope h₂] at h
  have : (handles s).idxOf r₁.rid = (handles s).idxOf r₂.rid := Option.some_inj.1 h
  rw [this, e₂] at e₁
  exact (Option.some_inj.1 e₁).symm

/-- Every index below the size of the scope is a live handle of a (unique) in-scope resource. -/
theorem handle_surjective {s : Scope} {i : ℕ} (hi : i < s.allowed.card) :
    ∃ r, InScope s r ∧ encode s r = some i ∧ decode s i = some r := by
  have hlt : i < (handles s).length := by simpa [length_handles] using hi
  refine ⟨⟨s.tenant, (handles s)[i]⟩, ?_⟩
  have hdec : decode s i = some ⟨s.tenant, (handles s)[i]⟩ := by
    unfold decode
    rw [List.getElem?_eq_getElem hlt]
    simp
  obtain ⟨hs, henc, -⟩ := decode_sound hdec
  exact ⟨hs, henc, hdec⟩

/-! ### A concrete instance, showing the model is not vacuous -/

section Example

/-- Tenant `0` may see resources `3` and `7`. -/
private def demoScope : Scope := ⟨0, {3, 7}⟩

example : InScope demoScope ⟨0, 7⟩ := by decide

private lemma handles_demoScope : handles demoScope = [3, 7] := by
  rw [handles, demoScope,
    Finset.sort_insert (r := (· ≤ ·)) (by simp) (by simp), Finset.sort_singleton]

example : encode demoScope ⟨0, 7⟩ = some 1 := by
  rw [encode_of_inScope (by decide), handles_demoScope]
  rfl

example : decode demoScope 1 = some ⟨0, 7⟩ := by
  rw [decode, handles_demoScope]
  rfl

/-- The same resource identifier owned by a different tenant is refused. -/
example : encode demoScope ⟨1, 7⟩ = none := by decide

/-- An identifier outside the scope's allow-list is refused. -/
example : encode demoScope ⟨0, 5⟩ = none := by decide

end Example

end PCA.Isolation


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

