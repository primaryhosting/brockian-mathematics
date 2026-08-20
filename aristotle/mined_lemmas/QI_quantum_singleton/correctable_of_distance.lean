/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Module Kronecker ComplexOrder

namespace QI

/-! ## Linear algebra preliminaries -/

/-- Swap the first two factors of a triple product type. -/

lemma correctable_of_distance {d : ℕ}
    (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n)
    (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (hd : HasDistanceGE M d) (ha : a < d)
    (u u' : Fin a → Fin q) :
    ∃ lam : ℂ, ∀ i j : Fin K,
      ∑ p : (Fin b → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M (glue e (u, p.1, p.2)) i) * M (glue e (u', p.1, p.2)) j
        = lam * (if i = j then 1 else 0) := by
  classical
  set A := firstBlock e with hA
  set F : (Fin n → Fin q) → (Fin n → Fin q) → ℂ := fun x y =>
    (if (∀ s : Fin a, x (e (Sum.inl (Sum.inl s))) = u s) then (1:ℂ) else 0) *
    (if (∀ s : Fin a, y (e (Sum.inl (Sum.inl s))) = u' s) then (1:ℂ) else 0) with hF
  set E : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ := Matrix.of fun x y =>
    if (∀ i ∉ A, x i = y i) then F x y else 0 with hE
  have hsupp : SupportedOn A E := by
    refine ⟨F, ?_, fun x y => rfl⟩
    intro x x' y y' hx hy
    have h1 : ∀ s : Fin a, x (e (Sum.inl (Sum.inl s))) = x' (e (Sum.inl (Sum.inl s))) :=
      fun s => hx _ ((mem_firstBlock_iff e _).mpr ⟨s, rfl⟩)
    have h2 : ∀ s : Fin a, y (e (Sum.inl (Sum.inl s))) = y' (e (Sum.inl (Sum.inl s))) :=
      fun s => hy _ ((mem_firstBlock_iff e _).mpr ⟨s, rfl⟩)
    simp only [hF, h1, h2]
  obtain ⟨lam, hlam⟩ := hd A E (by rw [hA, card_firstBlock]; exact ha) hsupp
  refine ⟨lam, fun i j => ?_⟩
  have hentry := congrFun (congrFun hlam i) j
  have hL : (Mᴴ * E * M) i j
      = ∑ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
          (starRingEnd ℂ) (M x i) * E x y * M y j := by
    rw [Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by simp [Matrix.conjTranspose_apply]
  have hEg : ∀ P Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
      E (glue e P) (glue e Q)
        = (if P.1 = u then (1:ℂ) else 0) * (if Q.1 = u' then 1 else 0) *
          (if P.2 = Q.2 then 1 else 0) := by
    intro P Q
    have h1 : (∀ s : Fin a, glue (q := q) e P (e (Sum.inl (Sum.inl s))) = u s) ↔ P.1 = u := by
      constructor
      · intro h; funext s; rw [← glue_inll e P s]; exact h s
      · intro h s; rw [glue_inll e P s, h]
    have h2 : (∀ s : Fin a, glue (q := q) e Q (e (Sum.inl (Sum.inl s))) = u' s) ↔ Q.1 = u' := by
      constructor
      · intro h; funext s; rw [← glue_inll e Q s]; exact h s
      · intro h s; rw [glue_inll e Q s, h]
    simp only [hE, Matrix.of_apply, hF, hA, glue_agree_off e P Q, h1, h2]
    split_ifs <;> ring
  have s1 : ∀ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
        (starRingEnd ℂ) (M x i) * E x y * M y j
      = ∑ Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
          (starRingEnd ℂ) (M x i) * E x (glue e Q) * M (glue e Q) j := fun x =>
    (Fintype.sum_bijective (glue e) (glue_bijective e)
      (fun Q => (starRingEnd ℂ) (M x i) * E x (glue e Q) * M (glue e Q) j)
      (fun y => (starRingEnd ℂ) (M x i) * E x y * M y j) (fun Q => rfl)).symm
  have s2 := Fintype.sum_bijective (glue e) (glue_bijective e)
      (fun P => ∑ Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M (glue e P) i) * E (glue e P) (glue e Q) * M (glue e Q) j)
      (fun x => ∑ Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M x i) * E x (glue e Q) * M (glue e Q) j) (fun P => rfl)
  have hsum : ∑ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
        (starRingEnd ℂ) (M x i) * E x y * M y j
      = ∑ P : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
          ∑ Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
          (starRingEnd ℂ) (M (glue e P) i) * E (glue e P) (glue e Q) * M (glue e Q) j := by
    simp_rw [s1]
    exact s2.symm
  rw [hL, hsum] at hentry
  simp only [hEg] at hentry
  have hone : ((lam • (1 : Matrix (Fin K) (Fin K) ℂ)) i j) = lam * (if i = j then 1 else 0) := by
    simp [Matrix.one_apply]
  rw [hone] at hentry
  rw [← hentry]
  exact (sum_indicator_collapse (A' := Fin a → Fin q)
    (P := (Fin b → Fin q) × (Fin c → Fin q))
    (fun w p => (starRingEnd ℂ) (M (glue e (w, p)) i)) (fun w p => M (glue e (w, p)) j) u u').symm

/-- If a code of dimension `K` in `(ℂ^q)^{⊗n}` has distance greater than the sizes of two
disjoint coordinate blocks of sizes `a` and `b`, then `K ≤ q ^ c`, where `c` is the number of
remaining coordinates. -/
