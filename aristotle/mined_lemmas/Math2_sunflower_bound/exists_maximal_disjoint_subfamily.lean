import Mathlib
/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of finite sets is a *sunflower with core `K`* if any two distinct members
of `S` meet exactly in `K`. -/

theorem exists_maximal_disjoint_subfamily (F : Finset (Finset α)) :
    ∃ P ⊆ F, PairwiseDisjointFamily P ∧
      ∀ A ∈ F, A.Nonempty → ∃ B ∈ P, (A ∩ B).Nonempty := by
  classical
  set PDfams : Finset (Finset (Finset α)) :=
    F.powerset.filter (fun P => PairwiseDisjointFamily P) with hPDfams
  have hne : PDfams.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [hPDfams, PairwiseDisjointFamily]
  obtain ⟨P, hP, hPmax⟩ := Finset.exists_max_image PDfams Finset.card hne
  rw [hPDfams, Finset.mem_filter, Finset.mem_powerset] at hP
  obtain ⟨hPF, hPD⟩ := hP
  refine ⟨P, hPF, hPD, ?_⟩
  intro A hAF hAne
  by_cases hAP : A ∈ P
  · exact ⟨A, hAP, by simpa using hAne⟩
  · by_contra hcon
    push_neg at hcon
    have hdisj : ∀ B ∈ P, A ∩ B = ∅ := hcon
    have hmem : insert A P ∈ PDfams := by
      rw [hPDfams, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hAF hPF, ?_⟩
      intro X hX Y hY hXY
      rcases Finset.mem_insert.1 hX with rfl | hX'
      · rcases Finset.mem_insert.1 hY with rfl | hY'
        · exact absurd rfl hXY
        · exact hdisj Y hY'
      · rcases Finset.mem_insert.1 hY with rfl | hY'
        · rw [Finset.inter_comm]; exact hdisj X hX'
        · exact hPD X hX' Y hY' hXY
    have := hPmax _ hmem
    rw [Finset.card_insert_of_notMem hAP] at this
    omega

/-- The Erdős–Rado sunflower lemma, proved by induction on the uniformity `w`
(auxiliary version, assuming `2 ≤ r`). -/
