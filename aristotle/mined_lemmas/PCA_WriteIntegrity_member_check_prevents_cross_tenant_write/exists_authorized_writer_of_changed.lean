/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.WriteIntegrity

/-- Tenant identifiers. -/
abbrev Tenant := Nat
/-- Principal (user / service account) identifiers. -/
abbrev Principal := Nat
/-- Resource identifiers. -/
abbrev ResourceId := Nat
/-- Values stored in resources. -/
abbrev Value := Nat

/-- The isolation policy of the engine: which principals are members of which
tenant, and which tenant owns which resource. -/
structure Policy where
  /-- `member p t` holds when principal `p` is a member of tenant `t`. -/
  member : Principal → Tenant → Bool
  /-- `owner i` is the tenant owning resource `i`. -/
  owner : ResourceId → Tenant

/-- A write request: an actor asking to set a resource to a value. -/
structure WriteReq where
  /-- The principal issuing the request. -/
  actor : Principal
  /-- The resource to be written. -/
  target : ResourceId
  /-- The value to be written. -/
  value : Value

/-- The state of the store: a value for every resource. -/
abbrev Store := ResourceId → Value

/-- Point update of the store. -/

theorem exists_authorized_writer_of_changed
    (P : Policy) (s : Store) (trace : List WriteReq) (i : ResourceId)
    (h : run P s trace i ≠ s i) :
    ∃ r ∈ trace, r.target = i ∧ authorized P r ∧ P.member r.actor (P.owner i) := by
  induction trace generalizing s with
  | nil => exact absurd rfl h
  | cons r rs ih =>
      by_cases hstep : step P s r i = s i
      · obtain ⟨q, hq, hq1, hq2, hq3⟩ := ih (step P s r) (by rw [hstep]; exact h)
        exact ⟨q, List.mem_cons_of_mem _ hq, hq1, hq2, hq3⟩
      · obtain ⟨htgt, hauth⟩ := step_ne_imp P s r i hstep
        refine ⟨r, by simp, htgt, hauth, ?_⟩
        rw [authorized, htgt] at hauth
        exact hauth

/-- Completeness of the engine: a legitimate in-tenant write does take effect. -/
