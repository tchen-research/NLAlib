import NLAlib.Matrix.Norms.BilinearSquareMass
import NLAlib.Matrix.Norms.GramSquareMassDeletion
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Attaining and scaling actual Euclidean bilinear probes

Named spectral norms are attained on the actual closed unit balls. Bounds
for general probes and a positive common radius supply the bilinear square
energy needed by resolvent concentration. Empty dimensions are included.
-/

noncomputable section
set_option autoImplicit false
open Matrix Finset
open scoped Matrix
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem inner_eq_star_dotProduct (A : Matrix n n ℂ)
    (v w : EuclideanSpace ℂ n) :
    inner ℂ v (WithLp.toLp 2 (A *ᵥ w.ofLp)) = star v.ofLp ⬝ᵥ (A *ᵥ w.ofLp) := by
  rw [← WithLp.toLp_ofLp 2 v, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

open scoped Matrix.Norms.L2Operator in
/-- The native bilinear probe is bounded by the two Euclidean lengths and the named spectral norm. -/
theorem norm_star_dotProduct_mulVec_le (A : Matrix n n ℂ) (v w : EuclideanSpace ℂ n) :
    ‖star v.ofLp ⬝ᵥ (A *ᵥ w.ofLp)‖ ≤ ‖v‖ * specNorm A * ‖w‖ := by
  have hi := norm_inner_le_norm (𝕜 := ℂ) v (WithLp.toLp 2 (A *ᵥ w.ofLp))
  rw [inner_eq_star_dotProduct] at hi
  calc _ ≤ ‖v‖ * ‖WithLp.toLp 2 (A *ᵥ w.ofLp)‖ := hi
    _ ≤ ‖v‖ * (specNorm A * ‖w‖) :=
      mul_le_mul_of_nonneg_left (A.l2_opNorm_mulVec w) (norm_nonneg _)
    _ = _ := by ring

/-- A bilinear test at two closed-unit-ball probes is bounded by the named spectral norm. -/
theorem norm_star_dotProduct_mulVec_le_specNorm (A : Matrix n n ℂ)
    (v w : EuclideanSpace ℂ n) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖star v.ofLp ⬝ᵥ (A *ᵥ w.ofLp)‖ ≤ specNorm A := by
  calc _ ≤ ‖v‖ * specNorm A * ‖w‖ := norm_star_dotProduct_mulVec_le A v w
    _ ≤ 1 * specNorm A * ‖w‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv (specNorm_nonneg _)) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul, mul_one] using
      mul_le_mul_of_nonneg_left hw (specNorm_nonneg A)

omit [DecidableEq n] in
private theorem norm_inner_normalize (z : EuclideanSpace ℂ n) :
    ‖inner ℂ (NormedSpace.normalize z) z‖ = ‖z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  unfold NormedSpace.normalize
  rw [← algebraMap_smul ℂ (‖z‖⁻¹) z, RCLike.algebraMap_eq_ofReal,
    inner_smul_real_left, inner_self_eq_norm_sq_to_K, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg z)]
  field_simp [hn]

/-- The actual named matrix spectral norm is attained at an actual pair of
Euclidean closed-unit-ball probes, including zero and empty matrices. -/
theorem exists_unitBall_bilinear_eq_specNorm (A : Matrix n n ℂ) :
    ∃ v w : EuclideanSpace ℂ n, ‖v‖ ≤ 1 ∧ ‖w‖ ≤ 1 ∧
      ‖star v.ofLp ⬝ᵥ (A *ᵥ w.ofLp)‖ = specNorm A := by
  obtain ⟨w, hw, he⟩ := exists_specNorm_sum_gram_eq (fun _ : Unit => A) Finset.univ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_nsmul] at he
  let z : EuclideanSpace ℂ n := WithLp.toLp 2 (A *ᵥ w.ofLp)
  have hz : ‖z‖ = specNorm A := by
    apply (sq_eq_sq₀ (norm_nonneg z) (specNorm_nonneg A)).mp
    simpa only [← specNorm_sq_eq_specNorm_conjTranspose_mul_self] using he.symm
  by_cases hzero : z = 0
  · refine ⟨0, w, by simp, hw, ?_⟩
    have hA : specNorm A = 0 := by rw [← hz, hzero, norm_zero]
    simp [hA]
  · refine ⟨NormedSpace.normalize z, w, (NormedSpace.norm_normalize hzero).le, hw, ?_⟩
    rw [← inner_eq_star_dotProduct]
    exact (norm_inner_normalize z).trans hz

omit [DecidableEq n] in
private theorem norm_bilinear_smul_real (A : Matrix n n ℂ)
    (v w : EuclideanSpace ℂ n) (a b : ℝ) :
    ‖star (a • v).ofLp ⬝ᵥ (A *ᵥ (b • w).ofLp)‖ =
      |a| * |b| * ‖star v.ofLp ⬝ᵥ (A *ᵥ w.ofLp)‖ := by
  simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, star_smul, star_trivial,
    smul_dotProduct, dotProduct_smul, smul_smul, norm_smul, Real.norm_eq_abs, abs_mul]
  ring

omit [DecidableEq n] in
/-- Actual bounded probes give a bilinear-energy bound with the exact fourth
power of their common radius. No maximizing probes are assumed. -/
theorem sum_bilinear_sq_le_mul_bilinearSquareMass
    (D : ι → Matrix n n ℂ) (s : Finset ι) (v w : EuclideanSpace ℂ n)
    {c : ℝ} (hc : 0 < c) (hv : ‖v‖ ≤ c) (hw : ‖w‖ ≤ c) :
    ∑ i ∈ s, ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2 ≤
      c ^ 4 * bilinearSquareMass D s := by
  let v' : EuclideanSpace ℂ n := c⁻¹ • v
  let w' : EuclideanSpace ℂ n := c⁻¹ • w
  have hv' : ‖v'‖ ≤ 1 := by
    dsimp [v']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), inv_mul_eq_div]
    exact (div_le_one hc).mpr hv
  have hw' : ‖w'‖ ≤ 1 := by
    dsimp [w']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), inv_mul_eq_div]
    exact (div_le_one hc).mpr hw
  have hve : c • v' = v := by dsimp [v']; rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hwe : c • w' = w := by dsimp [w']; rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hi (i : ι) : ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2 =
      c ^ 4 * ‖star v'.ofLp ⬝ᵥ (D i *ᵥ w'.ofLp)‖ ^ 2 := by
    rw [← hve, ← hwe, norm_bilinear_smul_real, abs_of_pos hc]
    ring
  calc
    _ = c ^ 4 * (∑ i ∈ s, ‖star v'.ofLp ⬝ᵥ (D i *ᵥ w'.ofLp)‖ ^ 2) := by
      simp_rw [hi]
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_bilinear_sq_le_bilinearSquareMass D s v' w' hv' hw') (by positivity)

end NLAlib
