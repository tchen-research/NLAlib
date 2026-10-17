import NLAlib.Matrix.Perturbation.InverseEigenvalueRootSum
import NLAlib.ForMathlib.Analysis.Complex.SchwarzExtension

/-!
# Gluing the actual upper-root sum to exterior branches

The actual upper-root sum and its Schwarz reflection extend across the exterior
real rays using the selected inverse branches. The resulting function is
holomorphic on the slit-plane domain required for contour flattening and has
a global linear norm bound. Values on the remaining real segment are set to
zero; no boundary limits there are used.
This supports the planar proof of `trace-exponential-stahl`.
-/

noncomputable section

open Complex Set Filter
open scoped Matrix Topology ComplexConjugate

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual upper characteristic roots glue to a Schwarz-symmetric exterior
inverse family on an open slit-plane domain. The global bound includes the
real points and therefore controls every thin contour uniformly. -/
theorem exists_inversePencilUpperRootSum_extension
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ) (s : ℝ)
    (hs : ∀ i, s ≠ b i) {R : ℝ} (branch : n → ℂ → ℂ)
    (hdiff : ∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖})
    (hspec : ∀ u, R < ‖u‖ → ∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
      (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ))))
    (hroot : ∀ u, R < ‖u‖ → 0 < u.im →
      inversePencilUpperRootSum A (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) u =
        ∑ i, if b i < s then branch i u else 0)
    (href : ∀ i u, R < ‖u‖ → branch i (conj u) = conj (branch i u)) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h ({u | u.im ≠ 0} ∪ {u | R < ‖u‖}) ∧
      (∀ u, R < ‖u‖ → h u = ∑ i, if b i < s then branch i u else 0) ∧
      (∀ u, 0 < u.im → h u =
        inversePencilUpperRootSum A (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) u) ∧
      (∀ u, h (conj u) = conj (h u)) ∧
      (∀ u, 0 < u.im → 0 ≤ (h u).im) ∧
      ∀ u, ‖h u‖ ≤ (Fintype.card n : ℝ) *
        specNorm (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ)))⁻¹ *
          (specNorm A + ‖u‖) := by
  classical
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))
  let f := inversePencilUpperRootSum A D
  let g : ℂ → ℂ := fun u => ∑ i, if b i < s then branch i u else 0
  let axis : ℂ → ℂ := fun u => if R < ‖u‖ then g u else 0
  let h := schwarzHalfPlaneExtension f axis
  have hDu : IsUnit D := isUnit_diagonal_sub_of_ne b s hs
  have hD : D.IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hf : ∀ u : ℂ, 0 < u.im → DifferentiableAt ℂ f u := by
    intro u hu
    exact (analyticAt_inversePencilUpperRootSum hA hD hDu (ne_of_gt hu)).differentiableAt
  have hg : DifferentiableOn ℂ g {u | R < ‖u‖} := by
    apply DifferentiableOn.fun_sum
    intro i _
    by_cases hi : b i < s
    · simpa only [if_pos hi] using hdiff i
    · simpa only [if_neg hi] using (differentiableOn_const (𝕜 := ℂ) (0 : ℂ) :
        DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) {u | R < ‖u‖})
  have haxis : DifferentiableOn ℂ axis {u | R < ‖u‖} := by
    apply hg.congr
    intro u hu
    change R < ‖u‖ at hu
    simp only [axis, if_pos hu]
  have hupp : ∀ u : ℂ, R < ‖u‖ → 0 < u.im → f u = axis u := by
    intro u hu him
    simpa only [axis, if_pos hu] using hroot u hu him
  have hrefg : ∀ u : ℂ, R < ‖u‖ → g (conj u) = conj (g u) := by
    intro u hu
    simp only [g, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [href i u hu]
  have hrefaxis : ∀ u : ℂ, R < ‖u‖ → axis (conj u) = conj (axis u) := by
    intro u hu
    simpa only [axis, norm_conj, if_pos hu] using hrefg u hu
  have hrefaxisall (u : ℂ) : axis (conj u) = conj (axis u) := by
    by_cases hu : R < ‖u‖
    · exact hrefaxis u hu
    · simp only [axis, norm_conj, if_neg hu, map_zero]
  have hgnorm (u : ℂ) (hu : R < ‖u‖) : ‖g u‖ ≤
      (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) := by
    apply norm_sum_ite_le_card_mul_specNorm_inv_of_det_pencil_eq_zero A D hDu u
      (fun i => branch i u)
    intro i
    apply (det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul A D hDu u _).mpr
    dsimp only [D]
    rw [inv_mul_sub_smul_one_diagonal_eq A b s hs u]
    exact (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mpr (hspec u hu i)
  refine ⟨h, differentiableOn_schwarzHalfPlaneExtension_union_exterior f axis hf haxis hupp
    hrefaxis, ?_, ?_, schwarzHalfPlaneExtension_conj_of_conj_eq_axis f axis hrefaxisall, ?_, ?_⟩
  · intro u hu
    simpa only [axis, if_pos hu] using
      schwarzHalfPlaneExtension_eq_of_conj_eq f axis hupp hrefaxis hu
  · intro u hu
    simp only [h, schwarzHalfPlaneExtension, if_pos hu]
    rfl
  · intro u hu
    simpa only [h, schwarzHalfPlaneExtension, if_pos hu] using
      inversePencilUpperRootSum_im_nonneg A D u
  · intro u
    have hC : 0 ≤ (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (specNorm_nonneg _))
        (add_nonneg (specNorm_nonneg _) (norm_nonneg _))
    dsimp only [h, schwarzHalfPlaneExtension]
    split_ifs with hpos hneg
    · exact norm_inversePencilUpperRootSum_le A D hDu u
    · simpa only [norm_conj] using norm_inversePencilUpperRootSum_le A D hDu (conj u)
    · dsimp only [axis]
      split_ifs with hu
      · exact hgnorm u hu
      · simpa only [norm_zero] using hC

end NLAlib
