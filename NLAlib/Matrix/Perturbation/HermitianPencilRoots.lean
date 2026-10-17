import NLAlib.Matrix.Norms.Core
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Root geometry of Hermitian matrix pencils

For `det (u I - A + z D) = 0`, a nonreal `u` excludes real `z` when `A` and
`D` are Hermitian. If `D` is invertible, every root has a uniform spectral-norm
bound on bounded sets of parameters. These are the root-separation and
boundedness inputs to the planar root-sum approach to Stahl's representation.
Source: Eremenko's exposition of Stahl's theorem, with the planar pencil
reorganization supplied in the accompanying derivation.
The associated atlas target is `trace-exponential-stahl`.
-/

noncomputable section

open Complex
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The pencil equation is precisely spectral membership in the forward pencil.
This formulation does not require invertibility of the slope matrix. -/
theorem det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum
    (A D : Matrix n n ℂ) (u z : ℂ) :
    (u • (1 : Matrix n n ℂ) - A + z • D).det = 0 ↔
      u ∈ spectrum ℂ (A - z • D) := by
  have heq : u • (1 : Matrix n n ℂ) - A + z • D =
      u • (1 : Matrix n n ℂ) - (A - z • D) := by abel
  rw [heq]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  simp only [isUnit_iff_ne_zero, not_not, Algebra.algebraMap_eq_smul_one]

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian pencil cannot have a real root in its slope variable at a
nonreal spectral parameter. In particular this applies throughout the open
upper half-plane, without any simplicity assumption on either matrix. -/
theorem im_ne_zero_of_det_hermitian_pencil_eq_zero
    {A D : Matrix n n ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian)
    {u z : ℂ} (hu : u.im ≠ 0)
    (hz : (u • (1 : Matrix n n ℂ) - A + z • D).det = 0) : z.im ≠ 0 := by
  intro hzim
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hzim]
  have hreal : (A - z • D).IsHermitian := by
    rw [← hzreal]
    exact hA.sub (hD.smul (by simp [IsSelfAdjoint]))
  exact hu (hreal.isSelfAdjoint.im_eq_zero_of_mem_spectrum
    ((det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum A D u z).mp hz))

/-- For an invertible slope matrix, a root of the pencil is an eigenvalue of
the inverse pencil. This retains algebraic multiplicities when used through
the characteristic polynomial. -/
theorem det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul
    (A D : Matrix n n ℂ) (hD : IsUnit D) (u z : ℂ) :
    (u • (1 : Matrix n n ℂ) - A + z • D).det = 0 ↔
      z ∈ spectrum ℂ (D⁻¹ * (A - u • (1 : Matrix n n ℂ))) := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  simp only [isUnit_iff_ne_zero, not_not, Algebra.algebraMap_eq_smul_one]
  have hfac : u • (1 : Matrix n n ℂ) - A + z • D =
      D * (z • (1 : Matrix n n ℂ) - D⁻¹ * (A - u • (1 : Matrix n n ℂ))) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left D _ (D.isUnit_iff_isUnit_det.mp hD)]
    abel
  rw [hfac, Matrix.det_mul]
  exact mul_eq_zero.trans (or_iff_right (D.isUnit_iff_isUnit_det.mp hD).ne_zero)

open scoped Matrix.Norms.L2Operator in
/-- Every root of an invertible matrix pencil is bounded by
`‖D⁻¹‖₂ (‖A‖₂ + |u|)`. The bound is uniform even when roots collide. -/
theorem norm_le_specNorm_inv_mul_of_det_pencil_eq_zero
    (A D : Matrix n n ℂ) (hD : IsUnit D) {u z : ℂ}
    (hz : (u • (1 : Matrix n n ℂ) - A + z • D).det = 0) :
    ‖z‖ ≤ specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have := hn
    simp at hz
  | inr hn =>
    have := hn
    have hspec :=
      (det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul A D hD u z).mp hz
    calc
      ‖z‖ ≤ ‖D⁻¹ * (A - u • (1 : Matrix n n ℂ))‖ :=
        spectrum.norm_le_norm_of_mem hspec
      _ ≤ ‖D⁻¹‖ * ‖A - u • (1 : Matrix n n ℂ)‖ := norm_mul_le _ _
      _ ≤ ‖D⁻¹‖ * (‖A‖ + ‖u‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [norm_smul, norm_one, mul_one] using
          norm_sub_le A (u • (1 : Matrix n n ℂ))
      _ = _ := rfl

/-- The actual roots of the inverse characteristic polynomial avoid the real
axis at every nonreal parameter of a Hermitian pencil. Algebraic
multiplicities are retained in `Polynomial.roots`. -/
theorem im_ne_zero_of_mem_roots_charpoly_inv_mul
    {A D : Matrix n n ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian)
    (hDu : IsUnit D) {u z : ℂ} (hu : u.im ≠ 0)
    (hz : z ∈ (D⁻¹ * (A - u • (1 : Matrix n n ℂ))).charpoly.roots) :
    z.im ≠ 0 := by
  have hs := Matrix.mem_spectrum_of_isRoot_charpoly
    ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hz)
  exact im_ne_zero_of_det_hermitian_pencil_eq_zero hA hD hu
    ((det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul A D hDu u z).mpr hs)

/-- The inverse characteristic roots have a common bound, independently of
their multiplicities and without requiring a Hermitian pencil. -/
theorem norm_le_specNorm_inv_mul_of_mem_roots_charpoly
    (A D : Matrix n n ℂ) (hD : IsUnit D) {u z : ℂ}
    (hz : z ∈ (D⁻¹ * (A - u • (1 : Matrix n n ℂ))).charpoly.roots) :
    ‖z‖ ≤ specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  have hs := Matrix.mem_spectrum_of_isRoot_charpoly
    ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hz)
  exact norm_le_specNorm_inv_mul_of_det_pencil_eq_zero A D hD
    ((det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul A D hD u z).mpr hs)

/-- Any submultiset of inverse characteristic roots has a dimension-times-root
bound. In particular this supplies the uniform bound for the sum of all upper
half-plane roots, including collisions. -/
theorem norm_sum_le_card_mul_specNorm_inv_of_le_roots_charpoly
    (A D : Matrix n n ℂ) (hD : IsUnit D) (u : ℂ) (roots : Multiset ℂ)
    (hroots : roots ≤ (D⁻¹ * (A - u • (1 : Matrix n n ℂ))).charpoly.roots) :
    ‖roots.sum‖ ≤ (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  let C := specNorm D⁻¹ * (specNorm A + ‖u‖)
  have hC : 0 ≤ C := mul_nonneg (specNorm_nonneg _) (add_nonneg (specNorm_nonneg _) (norm_nonneg _))
  have hcard : roots.card ≤ Fintype.card n := by
    exact (Multiset.card_le_card hroots).trans
      ((Polynomial.card_roots' _).trans (by rw [Matrix.charpoly_natDegree_eq_dim]))
  calc
    ‖roots.sum‖ ≤ (roots.map (fun z => ‖z‖)).sum := norm_multiset_sum_le roots
    _ ≤ roots.card • C := by
      simpa only [Multiset.card_map] using
        Multiset.sum_le_card_nsmul (roots.map (fun z => ‖z‖)) C (by
          intro x hx
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
          exact norm_le_specNorm_inv_mul_of_mem_roots_charpoly A D hD
            (Multiset.mem_of_le hroots hz))
    _ ≤ (Fintype.card n : ℝ) * C := by
      simpa only [nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard : (roots.card : ℝ) ≤ Fintype.card n) hC
    _ = _ := by dsimp [C]; ring

/-- A selected finite list of pencil roots has the same uniform bound.
This form applies to exterior branches at real parameter values as well as
to the upper-root multiset at nonreal parameters. -/
theorem norm_sum_ite_le_card_mul_specNorm_inv_of_det_pencil_eq_zero
    (A D : Matrix n n ℂ) (hD : IsUnit D) (u : ℂ) (ev : n → ℂ)
    (hev : ∀ i, (u • (1 : Matrix n n ℂ) - A + ev i • D).det = 0)
    (p : n → Prop) [DecidablePred p] :
    ‖∑ i, if p i then ev i else 0‖ ≤
      (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  let C := specNorm D⁻¹ * (specNorm A + ‖u‖)
  have hC : 0 ≤ C := mul_nonneg (specNorm_nonneg _) (add_nonneg (specNorm_nonneg _) (norm_nonneg _))
  calc
    ‖∑ i, if p i then ev i else 0‖ ≤ ∑ i, ‖if p i then ev i else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : n, C := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact norm_le_specNorm_inv_mul_of_det_pencil_eq_zero A D hD (hev i)
      · simpa only [norm_zero] using hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [C]; ring

end NLAlib
