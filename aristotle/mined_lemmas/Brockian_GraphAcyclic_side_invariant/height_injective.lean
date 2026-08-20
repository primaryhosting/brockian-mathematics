import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

lemma height_injective (h3 : Nat.Coprime 3 M) : Function.Injective (height M) := by
  intro a b hab
  simp [height] at hab
  have h1 : (a * 3⁻¹ : ZMod M).val = (b * 3⁻¹ : ZMod M).val := by
    have : ((a * 3⁻¹ : ZMod M).val : ℤ) = ((b * 3⁻¹ : ZMod M).val : ℤ) := by
      rw [ZMod.cast.eq_def] at hab
      rcases M with _ | M <;> simp_all
    exact Nat.cast_inj.mp this
  have h2 : ((a : ZMod M) * 3⁻¹) = ((b : ZMod M) * 3⁻¹) := by
    apply ZMod.val_injective M
    exact h1
  have h3' : IsUnit (3 : ZMod M) := by
    rw [isUnit_iff_exists_inv]
    use (3 : ZMod M)⁻¹
    exact three_mul_inv h3
  have h3'' : IsUnit ((3 : ZMod M)⁻¹) := by
    rw [isUnit_iff_exists_inv]
    use (3 : ZMod M)
    have := three_mul_inv h3
    rw [mul_comm] at this
    exact this
  have inv_mul : (3 : ZMod M)⁻¹ * 3 = 1 := by
    have h := three_mul_inv h3
    rw [mul_comm] at h
    simpa using h
  have h3''' : (a : ZMod M) = (b : ZMod M) := by
    calc (a : ZMod M) = (a : ZMod M) * 3⁻¹ * 3 := by rw [mul_assoc, inv_mul, mul_one]
      _ = (b : ZMod M) * 3⁻¹ * 3 := by rw [h2]
      _ = (b : ZMod M) := by rw [mul_assoc, inv_mul, mul_one]
  exact Subtype.ext h3'''

