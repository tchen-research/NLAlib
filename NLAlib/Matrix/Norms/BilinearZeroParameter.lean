import NLAlib.Matrix.Norms.BilinearProbes

/-! # Zero actual bilinear weak variance means zero coefficients -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- The actual attained coefficient energy vanishes precisely for the
zero coefficient family. Empty coordinate and coefficient types are
included. This supplies the deterministic zero-weak-variance case of
Gaussian spectral comparison. -/
theorem bilinearSquareMass_univ_eq_zero_iff (A : ι → Matrix n n ℂ) :
    bilinearSquareMass A Finset.univ = 0 ↔ ∀ i, A i = 0 := by
  constructor
  · intro hzero i
    ext a b
    let v : EuclideanSpace ℂ n := WithLp.toLp 2 (Pi.single a 1)
    let w : EuclideanSpace ℂ n := WithLp.toLp 2 (Pi.single b 1)
    have hv : ‖v‖ ≤ 1 := by simp [v]
    have hw : ‖w‖ ≤ 1 := by simp [w]
    have hs := sum_bilinear_sq_le_bilinearSquareMass A Finset.univ v w hv hw
    rw [hzero] at hs
    have hprobe (j : ι) : star v.ofLp ⬝ᵥ (A j *ᵥ w.ofLp) = A j a b := by
      change star (Pi.single a (1 : ℂ)) ⬝ᵥ (A j *ᵥ Pi.single b 1) = _
      rw [Pi.star_single, star_one, Matrix.mulVec_single_one, single_one_dotProduct]
      rfl
    have he : ∑ j, ‖A j a b‖ ^ 2 ≤ 0 := by
      simpa only [hprobe] using hs
    have hi : ‖A i a b‖ ^ 2 ≤ ∑ j, ‖A j a b‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖A j a b‖) (Finset.mem_univ i)
    have hn : ‖A i a b‖ = 0 := by nlinarith [norm_nonneg (A i a b)]
    simpa only [Matrix.zero_apply] using norm_eq_zero.mp hn
  · intro hzero
    obtain ⟨v, w, _, _, he⟩ := exists_bilinearSquareMass_eq A Finset.univ
    rw [he]
    simp only [hzero, Matrix.zero_mulVec, dotProduct_zero, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]

end NLAlib
