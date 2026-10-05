/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
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

set_option grind.warning false

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- `phi n` is the partial function computed by the program with index `n`
(the standard enumeration of partial recursive functions, obtained from the
Gödel numbering of `Nat.Partrec.Code`). -/
noncomputable def phi (n : ℕ) : ℕ →. ℕ :=
  Code.eval (Denumerable.ofNat Code n)

theorem phi_encode (c : Code) : phi (Encodable.encode c) = Code.eval c := by
  simp [phi, Denumerable.ofNat_encode]

/-- Every partial recursive function has an index. -/
theorem exists_index {f : ℕ →. ℕ} (hf : Nat.Partrec f) : ∃ n, phi n = f := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  exact ⟨Encodable.encode c, by rw [phi_encode, hc]⟩

/-- **Rice's theorem** (index-set form). Let `A` be a set of program indices which is
*semantic* (extensional): membership of an index in `A` depends only on the partial
function that index computes. If `A` is *nontrivial*, i.e. it is neither empty nor all of
`ℕ`, then `A` is not recursive (decidable). -/
theorem rice_extended (A : Set ℕ)
    (hsem : ∀ m n : ℕ, phi m = phi n → (m ∈ A ↔ n ∈ A))
    (hne : A.Nonempty) (hnu : Aᶜ.Nonempty) :
    ¬ ComputablePred (fun n : ℕ => n ∈ A) := by
  intro hA
  classical
  -- Transport `A` to a set of codes.
  set C : Set Code := {c : Code | Encodable.encode c ∈ A} with hC
  -- `C` is extensional.
  have hext : ∀ cf cg : Code, Code.eval cf = Code.eval cg → (cf ∈ C ↔ cg ∈ C) := by
    intro cf cg h
    exact hsem _ _ (by rw [phi_encode, phi_encode, h])
  -- `C` is decidable, since `A` is.
  have hCcomp : ComputablePred (fun c : Code => c ∈ C) := by
    obtain ⟨_, h⟩ := hA
    exact ⟨by infer_instance, by
      simpa [hC] using h.comp (Computable.encode (α := Code))⟩
  -- Rice's theorem for codes.
  rcases (ComputablePred.rice₂ C hext).1 hCcomp with h | h
  · obtain ⟨a, ha⟩ := hne
    have : (Denumerable.ofNat Code a) ∈ C := by
      simpa [hC, Denumerable.encode_ofNat] using ha
    rw [h] at this
    exact this
  · obtain ⟨b, hb⟩ := hnu
    have : (Denumerable.ofNat Code b) ∈ C := by rw [h]; trivial
    simp only [hC, Set.mem_setOf_eq, Denumerable.encode_ofNat] at this
    exact hb this

/-- Consequence: the halting set `{n | phi n n is defined}` (the diagonal halting problem)
is not recursive. Note that this set is *not* semantic, so it is derived directly from
Mathlib's halting problem rather than from `rice_extended`. -/
theorem halting_not_computable (m : ℕ) :
    ¬ ComputablePred (fun n : ℕ => (phi n m).Dom) := by
  intro h
  refine ComputablePred.halting_problem m ?_
  obtain ⟨_, h⟩ := h
  refine ⟨by infer_instance, ?_⟩
  simpa [phi, Denumerable.ofNat_encode] using h.comp (Computable.encode (α := Code))

/-- An instance of `rice_extended`: the set of indices of programs computing the
everywhere-undefined function is not recursive. -/
theorem index_of_empty_not_computable :
    ¬ ComputablePred (fun n : ℕ => n ∈ {n : ℕ | phi n = fun _ => Part.none}) := by
  refine rice_extended _ (fun m n h => by simp [Set.mem_setOf_eq, h]) ?_ ?_
  · obtain ⟨n, hn⟩ := exists_index (f := fun _ => Part.none) Nat.Partrec.none
    exact ⟨n, by simpa using hn⟩
  · obtain ⟨n, hn⟩ := exists_index (Nat.Partrec.of_primrec Nat.Primrec.id)
    refine ⟨n, ?_⟩
    intro hmem
    have h0 : phi n 0 = Part.none := by
      rw [(hmem : phi n = fun _ => Part.none)]
    rw [hn] at h0
    simp [Part.eq_none_iff'] at h0

end CS

#print axioms CS.rice_extended
#print axioms CS.halting_not_computable
#print axioms CS.index_of_empty_not_computable

