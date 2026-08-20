/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA
namespace WriteIntegrity

/-! ## The isolation engine model

A minimal multi-tenant key–value service.  Every principal belongs to a tenant and
every resource is owned by a tenant.  A write request is executed only if the
*member check* succeeds, i.e. the writing principal's tenant is exactly the tenant
owning the target resource.  Otherwise the request is dropped and the store is
unchanged. -/

/-- Tenant identifiers. -/
abbrev TenantId := Nat
/-- Principal (user / service account) identifiers. -/
abbrev PrincipalId := Nat
/-- Resource (record) identifiers. -/
abbrev ResourceId := Nat
/-- Values stored in resources. -/
abbrev Value := Nat

/-- The static environment: the tenant of each principal, and the owning tenant of
each resource. -/
structure Env where
  /-- The tenant a principal belongs to. -/
  tenantOf : PrincipalId → TenantId
  /-- The tenant owning a resource. -/
  ownerOf : ResourceId → TenantId

/-- A write request: a principal asks to store `value` into `resource`. -/
structure Request where
  /-- The requesting principal. -/
  principal : PrincipalId
  /-- The targeted resource. -/
  resource : ResourceId
  /-- The value to be written. -/
  value : Value

/-- The store maps every resource to its current value. -/
abbrev Store := ResourceId → Value

/-- The membership guard of the isolation engine: the principal's tenant must own
the targeted resource. -/
def memberCheck (E : Env) (r : Request) : Bool :=
  E.tenantOf r.principal == E.ownerOf r.resource

/-- Unguarded point update of the store. -/
def writeRaw (s : Store) (rid : ResourceId) (v : Value) : Store :=
  fun x => if x = rid then v else s x

/-- One guarded step of the engine: perform the write only if the member check passes. -/
def step (E : Env) (s : Store) (r : Request) : Store :=
  if memberCheck E r then writeRaw s r.resource r.value else s

/-- Executing a whole trace of requests. -/
def run (E : Env) (s : Store) (rs : List Request) : Store :=
  rs.foldl (step E) s

/-- A trace is *issued by tenant `t`* when every request in it comes from a principal
belonging to `t`. -/
def IssuedBy (E : Env) (t : TenantId) (rs : List Request) : Prop :=
  ∀ r ∈ rs, E.tenantOf r.principal = t

/-! ## Basic lemmas -/

@[simp] theorem memberCheck_iff (E : Env) (r : Request) :
    memberCheck E r = true ↔ E.tenantOf r.principal = E.ownerOf r.resource := by
  simp [memberCheck]

@[simp] theorem run_nil (E : Env) (s : Store) : run E s [] = s := rfl

@[simp] theorem run_cons (E : Env) (s : Store) (r : Request) (rs : List Request) :
    run E s (r :: rs) = run E (step E s r) rs := rfl

/-- A single guarded step cannot modify a resource which is not owned by the
requesting principal's tenant. -/
theorem step_eq_of_owner_ne (E : Env) (s : Store) (r : Request) (rid : ResourceId)
    (h : E.tenantOf r.principal ≠ E.ownerOf rid) : step E s r rid = s rid := by
  unfold step writeRaw
  by_cases hc : memberCheck E r
  · simp only [hc, if_true]
    by_cases hr : rid = r.resource
    · subst hr
      exact absurd ((memberCheck_iff E r).mp hc) h
    · simp [hr]
  · simp [hc]

/-- A step performing an authorized write really does store the value. -/
theorem step_apply_authorized (E : Env) (s : Store) (r : Request)
    (h : E.tenantOf r.principal = E.ownerOf r.resource) :
    step E s r r.resource = r.value := by
  simp [step, memberCheck, h, writeRaw]

/-- A step leaves untouched every resource other than its target. -/
theorem step_eq_of_ne_resource (E : Env) (s : Store) (r : Request) (rid : ResourceId)
    (h : rid ≠ r.resource) : step E s r rid = s rid := by
  by_cases hc : memberCheck E r <;> simp [step, writeRaw, hc, h]

/-! ## Main soundness theorem -/

/-- **Member check prevents cross-tenant writes.**

If every request in the trace `rs` is issued by a principal of tenant `t`, and the
resource `rid` is owned by a *different* tenant, then running the whole trace through
the guarded engine leaves `rid` completely unchanged. -/
theorem member_check_prevents_cross_tenant_write
    (E : Env) (s : Store) (t : TenantId) (rs : List Request) (rid : ResourceId)
    (htrace : IssuedBy E t rs) (howner : E.ownerOf rid ≠ t) :
    run E s rs rid = s rid := by
  induction rs generalizing s with
  | nil => simp
  | cons r rs ih =>
      have hr : E.tenantOf r.principal = t := htrace r (List.mem_cons_self ..)
      have htail : IssuedBy E t rs := fun q hq => htrace q (List.mem_cons_of_mem _ hq)
      have hstep : step E s r rid = s rid := by
        refine step_eq_of_owner_ne E s r rid ?_
        rw [hr]
        exact fun hcontra => howner hcontra.symm
      rw [run_cons, ih _ htail, hstep]

/-! ## Completeness: legitimate in-tenant writes are not blocked -/

/-- The engine is not vacuously safe: a request whose member check succeeds is executed. -/
theorem run_singleton_authorized (E : Env) (s : Store) (r : Request)
    (h : E.tenantOf r.principal = E.ownerOf r.resource) :
    run E s [r] r.resource = r.value :=
  step_apply_authorized E s r h

/-- Conversely, a *cross-tenant* single request is dropped entirely. -/
theorem run_singleton_unauthorized (E : Env) (s : Store) (r : Request)
    (h : E.tenantOf r.principal ≠ E.ownerOf r.resource) :
    run E s [r] = s := by
  funext x
  have hc : memberCheck E r = false := by
    unfold memberCheck
    exact beq_eq_false_iff_ne.mpr h
  simp [run, step, hc]

/-- Any change to the store at `rid` is witnessed by an authorized request in the trace
targeting `rid`. -/
theorem exists_authorized_request_of_changed
    (E : Env) (s : Store) (rs : List Request) (rid : ResourceId)
    (hne : run E s rs rid ≠ s rid) :
    ∃ r ∈ rs, r.resource = rid ∧ E.tenantOf r.principal = E.ownerOf rid := by
  induction rs generalizing s with
  | nil => simp at hne
  | cons r rs ih =>
      rw [run_cons] at hne
      by_cases hstep : step E s r rid = s rid
      · obtain ⟨q, hq, hq1, hq2⟩ := ih (step E s r) (by rw [hstep]; exact hne)
        exact ⟨q, List.mem_cons_of_mem _ hq, hq1, hq2⟩
      · refine ⟨r, List.mem_cons_self .., ?_, ?_⟩
        · exact Classical.byContradiction fun hres =>
            hstep (step_eq_of_ne_resource E s r rid fun h => hres h.symm)
        · exact Classical.byContradiction fun hown =>
            hstep (step_eq_of_owner_ne E s r rid hown)

/-! ## A concrete instance (non-vacuity check) -/

/-- Two tenants: principal `0` and resource `0` belong to tenant `0`, everything else
belongs to tenant `1`. -/
def demoEnv : Env where
  tenantOf p := if p = 0 then 0 else 1
  ownerOf r := if r = 0 then 0 else 1

/-- The empty store. -/
def emptyStore : Store := fun _ => 0

/-- Principal `0` (tenant `0`) cannot write into resource `1` (owned by tenant `1`). -/
theorem demo_cross_tenant_write_blocked :
    run demoEnv emptyStore [{ principal := 0, resource := 1, value := 7 }] 1 = 0 := by
  decide

/-- Principal `1` (tenant `1`) can write into resource `1` (owned by tenant `1`). -/
theorem demo_in_tenant_write_succeeds :
    run demoEnv emptyStore [{ principal := 1, resource := 1, value := 7 }] 1 = 7 := by
  decide

end WriteIntegrity
end PCA

