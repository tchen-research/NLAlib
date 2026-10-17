import NLAlib.Matrix.Perturbation.InverseEigenvalueBranches
import NLAlib.ForMathlib.Analysis.Complex.ExteriorHalfPlane
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Half-plane labels of inverse spectral branches

The inverse branch with slope `(s - bᵢ)⁻¹` lies in the upper half-plane exactly
when `bᵢ < s`, throughout the exterior upper half-plane. This verifies the
cluster selection used by the planar root-sum route to `trace-exponential-stahl`.
-/

noncomputable section

open Complex Filter
open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
private theorem inverse_branch_im_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (b : n → ℝ) (s : ℝ) {u z : ℂ} (hu : 0 < u.im)
    (hmem : u - (s : ℂ) * z ∈ spectrum ℂ
      (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) : z.im ≠ 0 := by
  intro hzim
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hzim]
  have hB : (Matrix.diagonal (fun i => (b i : ℂ))).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    simp [IsSelfAdjoint]
  have hreal : (A - z • Matrix.diagonal (fun i => (b i : ℂ))).IsHermitian := by
    rw [← hzreal]
    exact hA.sub (hB.smul (by simp [IsSelfAdjoint]))
  have him := hreal.isSelfAdjoint.im_eq_zero_of_mem_spectrum hmem
  have huim : u.im = 0 := by simpa [hzim] using him
  exact (ne_of_gt hu) huim

/-- For Hermitian `A`, the constructed exterior inverse branches are in the upper
half-plane precisely for indices with `bᵢ < s`. This proves the label selection at
every exterior parameter above the real axis, without assuming global simple roots.

atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_inverse_eigenvalue_branches_im_pos_iff
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖} ∧
        Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ)))) ∧
      (∀ u, R < ‖u‖ →
        (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
          (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i u)) ∧
      ∀ u, R < ‖u‖ → 0 < u.im → ∀ i, 0 < (branch i u).im ↔ b i < s := by
  obtain ⟨R, hR, branch, hbranch, hspec⟩ :=
    exists_exterior_inverse_eigenvalue_branches A b hb s hs
  refine ⟨R, hR, branch, hbranch, hspec, ?_⟩
  intro u hu him i
  have hreal : ∀ v, R < ‖v‖ → 0 < v.im → (branch i v).im ≠ 0 := by
    intro v hv hvi
    exact inverse_branch_im_ne_zero hA b s hvi ((hspec v hv).1 i)
  have hlim : Tendsto (fun v => branch i v - (((s - b i)⁻¹ : ℝ) : ℂ) * v)
      (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))) := by
    simpa only [Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using (hbranch i).2
  simpa only [inv_pos, sub_pos] using
    Complex.im_pos_iff_slope_pos_of_tendsto_affine
      (hbranch i).1.continuousOn hreal hlim (inv_ne_zero (sub_ne_zero.mpr (hs i))) hu him

end NLAlib
