import PCA.Isolation

/-
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Isolation

/-! ## The abstract isolation model

A *privilege policy* on a type of privileges `P` is a relation `grants`, where
`grants a b` means "a principal holding privilege `a` may directly acquire
privilege `b`".  Privilege *escalation* is the reflexive–transitive closure of
this relation, and the *escape set* of a set `S` of initially held privileges is
the set of privileges reachable by escalation from `S`. -/

/-- A privilege policy: `grants a b` means privilege `a` directly confers `b`. -/
structure Policy (P : Type*) where
  /-- The direct-grant relation of the policy. -/
  grants : P → P → Prop

variable {P : Type*}

/-- `Escalates pol a b` : privilege `b` is reachable from privilege `a` by a
finite chain of direct grants of the policy `pol`. -/
def Escalates (pol : Policy P) : P → P → Prop :=
  Relation.ReflTransGen pol.grants

/-- The privileges that can be escaped to, starting from the set `S`. -/
def escape (pol : Policy P) (S : Set P) : Set P :=
  {q | ∃ p ∈ S, Escalates pol p q}

/-- A policy is at most as permissive as another when each of its direct grants
is also a grant of the other. -/
def Permits (pol₁ pol₂ : Policy P) : Prop :=
  ∀ a b, pol₁.grants a b → pol₂.grants a b

@[inherit_doc] scoped infix:50 " ⊑ " => PCA.Isolation.Permits

theorem Permits.refl (pol : Policy P) : Permits pol pol := fun _ _ h => h

theorem Permits.trans {pol₁ pol₂ pol₃ : Policy P}
    (h₁ : Permits pol₁ pol₂) (h₂ : Permits pol₂ pol₃) : Permits pol₁ pol₃ :=
  fun a b h => h₂ a b (h₁ a b h)

theorem escalates_refl (pol : Policy P) (a : P) : Escalates pol a a :=
  Relation.ReflTransGen.refl

theorem escalates_trans {pol : Policy P} {a b c : P}
    (h₁ : Escalates pol a b) (h₂ : Escalates pol b c) : Escalates pol a c :=
  Relation.ReflTransGen.trans h₁ h₂

theorem escalates_of_grants {pol : Policy P} {a b : P} (h : pol.grants a b) :
    Escalates pol a b :=
  Relation.ReflTransGen.single h

/-- Escalation is monotone in the policy. -/
theorem escalates_mono {pol₁ pol₂ : Policy P} (h : Permits pol₁ pol₂) {a b : P}
    (hab : Escalates pol₁ a b) : Escalates pol₂ a b :=
  hab.mono (fun x y hxy => h x y hxy)

theorem subset_escape (pol : Policy P) (S : Set P) : S ⊆ escape pol S :=
  fun p hp => ⟨p, hp, escalates_refl pol p⟩

/-! ## The target theorem -/

/-- **Privilege escape is monotone.**  Weakening the isolation policy (allowing
more direct grants) and starting from a larger set of initially held privileges
can only enlarge the set of privileges reachable by escalation. -/
theorem priv_escape_monotone {pol₁ pol₂ : Policy P} {S₁ S₂ : Set P}
    (hpol : Permits pol₁ pol₂) (hS : S₁ ⊆ S₂) : escape pol₁ S₁ ⊆ escape pol₂ S₂ := by
  rintro q ⟨p, hp, hpq⟩
  exact ⟨p, hS hp, escalates_mono hpol hpq⟩

/-- Monotonicity in the policy alone. -/
theorem escape_mono_policy {pol₁ pol₂ : Policy P} (hpol : Permits pol₁ pol₂) (S : Set P) :
    escape pol₁ S ⊆ escape pol₂ S :=
  priv_escape_monotone hpol (subset_refl S)

/-- Monotonicity in the initial privilege set alone. -/
theorem escape_mono_set (pol : Policy P) {S₁ S₂ : Set P} (hS : S₁ ⊆ S₂) :
    escape pol S₁ ⊆ escape pol S₂ :=
  priv_escape_monotone (Permits.refl pol) hS

/-- The escape operator is idempotent: escalation cannot be bootstrapped. -/
theorem escape_escape (pol : Policy P) (S : Set P) :
    escape pol (escape pol S) = escape pol S := by
  apply Set.Subset.antisymm
  · rintro q ⟨p, ⟨r, hr, hrp⟩, hpq⟩
    exact ⟨r, hr, escalates_trans hrp hpq⟩
  · exact subset_escape pol (escape pol S)

/-! ## Isolation

Two sets of privileges are *isolated* under a policy when nothing in the escape
set of the first lies in the second. -/

/-- `Isolated pol S T` : no privilege of `T` is reachable by escalation from `S`. -/
def Isolated (pol : Policy P) (S T : Set P) : Prop :=
  escape pol S ∩ T = ∅

theorem isolated_iff (pol : Policy P) (S T : Set P) :
    Isolated pol S T ↔ ∀ p ∈ S, ∀ q ∈ T, ¬ Escalates pol p q := by
  constructor
  · intro h p hp q hq hpq
    have hmem : q ∈ escape pol S ∩ T := ⟨⟨p, hp, hpq⟩, hq⟩
    rw [h] at hmem
    exact hmem
  · intro h
    ext q
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨p, hp, hpq⟩ hq
    exact h p hp q hq hpq

/-- Isolation is *antitone*: it is preserved when the policy is tightened or the
sets are shrunk. -/
theorem isolated_mono {pol₁ pol₂ : Policy P} {S₁ S₂ T₁ T₂ : Set P}
    (hpol : Permits pol₁ pol₂) (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂)
    (h : Isolated pol₂ S₂ T₂) : Isolated pol₁ S₁ T₁ := by
  rw [isolated_iff] at h ⊢
  exact fun p hp q hq hpq => h p (hS hp) q (hT hq) (escalates_mono hpol hpq)

/-! ## The isolation engine

For a finite privilege type the escape set is computed by saturating the initial
set under the direct grants.  We show the engine is *sound* (it only reports
genuinely reachable privileges) and *complete* (it reports all of them). -/

section Engine

variable [DecidableEq P]

/-- A finitely presented policy: `grants p` lists the privileges directly
conferred by `p`. -/
structure FinPolicy (P : Type*) where
  /-- Direct grants of a privilege, as a finite set. -/
  grants : P → Finset P

/-- The abstract policy underlying a finitely presented one. -/
def FinPolicy.toPolicy (pol : FinPolicy P) : Policy P :=
  ⟨fun a b => b ∈ pol.grants a⟩

/-- One round of saturation: add everything directly granted by the current set. -/
def stepClosure (pol : FinPolicy P) (S : Finset P) : Finset P :=
  S ∪ S.biUnion pol.grants

/-- `iter pol S n` is the result of `n` rounds of saturation. -/
def iter (pol : FinPolicy P) (S : Finset P) (n : ℕ) : Finset P :=
  (stepClosure pol)^[n] S

/-- The isolation engine: the computed escape set of `S`. -/
def engineEscape [Fintype P] (pol : FinPolicy P) (S : Finset P) : Finset P :=
  iter pol S (Fintype.card P + 1)

theorem iter_zero (pol : FinPolicy P) (S : Finset P) : iter pol S 0 = S := rfl

theorem iter_succ (pol : FinPolicy P) (S : Finset P) (n : ℕ) :
    iter pol S (n + 1) = stepClosure pol (iter pol S n) := by
  simp [iter, Function.iterate_succ_apply']

theorem subset_stepClosure (pol : FinPolicy P) (S : Finset P) :
    S ⊆ stepClosure pol S := Finset.subset_union_left

theorem stepClosure_mono (pol : FinPolicy P) {S T : Finset P} (h : S ⊆ T) :
    stepClosure pol S ⊆ stepClosure pol T := by
  intro x hx
  simp only [stepClosure, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
  rcases hx with hx | ⟨a, ha, hax⟩
  · exact Or.inl (h hx)
  · exact Or.inr ⟨a, h ha, hax⟩

theorem iter_subset_succ (pol : FinPolicy P) (S : Finset P) (n : ℕ) :
    iter pol S n ⊆ iter pol S (n + 1) := by
  rw [iter_succ]
  exact subset_stepClosure pol _

theorem iter_mono (pol : FinPolicy P) (S : Finset P) {m n : ℕ} (h : m ≤ n) :
    iter pol S m ⊆ iter pol S n := by
  induction n with
  | zero =>
    rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hk | hk
    · exact (ih (Nat.lt_succ_iff.mp hk)).trans (iter_subset_succ pol S k)
    · have hmk : m = k + 1 := Nat.le_antisymm h hk
      subst hmk
      exact Finset.Subset.refl _

/-- **Soundness of the engine.**  Everything in `iter pol S n` is genuinely
reachable by escalation from `S`. -/
theorem mem_iter_sound (pol : FinPolicy P) (S : Finset P) (n : ℕ) {q : P}
    (hq : q ∈ iter pol S n) : ∃ p ∈ S, Escalates pol.toPolicy p q := by
  induction n generalizing q with
  | zero => exact ⟨q, hq, escalates_refl _ _⟩
  | succ k ih =>
    rw [iter_succ] at hq
    simp only [stepClosure, Finset.mem_union, Finset.mem_biUnion] at hq
    rcases hq with hq | ⟨a, ha, haq⟩
    · exact ih hq
    · obtain ⟨p, hp, hpa⟩ := ih ha
      exact ⟨p, hp, escalates_trans hpa (escalates_of_grants (pol := pol.toPolicy) haq)⟩

/-- Reachability by escalation is witnessed by some stage of the saturation. -/
theorem mem_iter_of_escalates (pol : FinPolicy P) (S : Finset P) {p q : P}
    (hp : p ∈ S) (h : Escalates pol.toPolicy p q) : ∃ n, q ∈ iter pol S n := by
  induction h with
  | refl => exact ⟨0, hp⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [iter_succ]
    simp only [stepClosure, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inr ⟨_, hn, hbc⟩

/-- If saturation stalls at stage `n` it has stalled forever. -/
theorem iter_stabilizes (pol : FinPolicy P) (S : Finset P) {n : ℕ}
    (h : iter pol S (n + 1) = iter pol S n) :
    ∀ m, n ≤ m → iter pol S m = iter pol S n := by
  intro m hm
  induction m with
  | zero => rw [Nat.le_zero.mp hm]
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with hk | hk
    · have hik := ih (Nat.lt_succ_iff.mp hk)
      rw [iter_succ, hik, ← iter_succ, h]
    · have hnk : n = k + 1 := Nat.le_antisymm hm hk
      rw [hnk]

/-- Before saturation stalls, each round adds at least one privilege. -/
theorem card_iter_ge (pol : FinPolicy P) (S : Finset P) (n : ℕ)
    (h : ∀ k < n, iter pol S (k + 1) ≠ iter pol S k) :
    n ≤ (iter pol S n).card := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ (iter pol S k).card := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hne : iter pol S (k + 1) ≠ iter pol S k := h k (Nat.lt_succ_self k)
    have hsub : iter pol S k ⊆ iter pol S (k + 1) := iter_subset_succ pol S k
    have hssub : iter pol S k ⊂ iter pol S (k + 1) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun hcontra => hne hcontra.symm⟩
    have hcard := Finset.card_lt_card hssub
    omega

/-- Saturation is complete after `Fintype.card P + 1` rounds. -/
theorem iter_subset_engine [Fintype P] (pol : FinPolicy P) (S : Finset P) (n : ℕ) :
    iter pol S n ⊆ engineEscape pol S := by
  by_cases hstall : ∀ k < Fintype.card P + 1, iter pol S (k + 1) ≠ iter pol S k
  · exfalso
    have h1 : Fintype.card P + 1 ≤ (iter pol S (Fintype.card P + 1)).card :=
      card_iter_ge pol S _ hstall
    have h2 : (iter pol S (Fintype.card P + 1)).card ≤ Fintype.card P :=
      Finset.card_le_univ _
    omega
  · push_neg at hstall
    obtain ⟨k, hkN, hk⟩ := hstall
    have hstab := iter_stabilizes pol S hk
    have hNk : iter pol S (Fintype.card P + 1) = iter pol S k := hstab _ (Nat.le_of_lt hkN)
    rcases Nat.lt_or_ge n k with hn | hn
    · rw [engineEscape, hNk]
      exact iter_mono pol S (Nat.le_of_lt hn)
    · rw [engineEscape, hNk, hstab n hn]

/-- **Soundness and completeness of the isolation engine.**  The computed escape
set is exactly the set of privileges reachable by escalation. -/
theorem engineEscape_eq [Fintype P] (pol : FinPolicy P) (S : Finset P) :
    (engineEscape pol S : Set P) = escape pol.toPolicy (S : Set P) := by
  ext q
  constructor
  · intro hq
    exact mem_iter_sound pol S _ (by simpa [engineEscape] using hq)
  · rintro ⟨p, hp, hpq⟩
    obtain ⟨n, hn⟩ := mem_iter_of_escalates pol S (by simpa using hp) hpq
    exact_mod_cast iter_subset_engine pol S n hn

/-- The engine decides isolation. -/
theorem engine_isolated_iff [Fintype P] (pol : FinPolicy P) (S T : Finset P) :
    engineEscape pol S ∩ T = ∅ ↔ Isolated pol.toPolicy (S : Set P) (T : Set P) := by
  rw [Isolated, ← engineEscape_eq]
  constructor
  · intro h
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro q ⟨hq, hqT⟩
    have hmem : q ∈ engineEscape pol S ∩ T :=
      Finset.mem_inter.mpr ⟨by exact_mod_cast hq, by exact_mod_cast hqT⟩
    rw [h] at hmem
    exact Finset.notMem_empty q hmem
  · intro h
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro q hq
    rw [Finset.mem_inter] at hq
    have hmem : q ∈ (engineEscape pol S : Set P) ∩ (T : Set P) :=
      ⟨by exact_mod_cast hq.1, by exact_mod_cast hq.2⟩
    rw [h] at hmem
    exact hmem

/-- Monotonicity of the engine, matching `priv_escape_monotone`. -/
theorem engineEscape_mono [Fintype P] {pol₁ pol₂ : FinPolicy P} {S₁ S₂ : Finset P}
    (hpol : ∀ a, pol₁.grants a ⊆ pol₂.grants a) (hS : S₁ ⊆ S₂) :
    (engineEscape pol₁ S₁ : Set P) ⊆ (engineEscape pol₂ S₂ : Set P) := by
  rw [engineEscape_eq, engineEscape_eq]
  exact priv_escape_monotone (fun a b hab => hpol a hab) (by exact_mod_cast hS)

end Engine

/-! ## A worked example

A three-privilege policy in which `0` grants `1` and `1` grants `2`.  The engine
computes the full escape set of `{0}` and certifies that `{2}` is isolated from
`{0, 1}`. -/

namespace Example

/-- `0 ⟶ 1 ⟶ 2`, and `2` grants nothing. -/
def chain : FinPolicy (Fin 3) :=
  ⟨fun p => if p = 0 then {1} else if p = 1 then {2} else ∅⟩

example : engineEscape chain {0} = {0, 1, 2} := by decide

example : Isolated chain.toPolicy ({2} : Finset (Fin 3)) ({0, 1} : Finset (Fin 3)) :=
  (engine_isolated_iff chain {2} {0, 1}).mp (by decide)

end Example

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

