import NLAlib.Probability.Free.WordMatrixDysonIdentity
import NLAlib.ForMathlib.Analysis.CStarAlgebra.SelfAdjointResolvent
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import NLAlib.Probability.Free.WordVacuumTrace
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The concrete native Dyson resolvent is holomorphic and height bounded

The function is defined by the genuine amplified vacuum coefficient of
the actual free linear model. Its Dyson identity, nonreal derivative and
reciprocal-height operator-norm bound are derived from that definition,
including empty dimensions and arbitrary Hermitian mean.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NLAlib
variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

open scoped Matrix.Norms.L2Operator in
/-- Actual vacuum compression bundled continuously for Euclidean matrix operator norm. -/
def wordMatrixVacuumCompressionCLM : M →L[ℂ] Matrix D D ℂ :=
  (wordMatrixVacuumCompression (D := D) (ι := ι)).mkContinuous
    (Fintype.card D : ℝ) (fun t => specNorm_wordMatrixVacuumCompression_le t)

/-- The actual native free resolvent compressed to its coefficient matrix. -/
def wordNativeDysonResolvent (A₀ : Matrix D D ℂ)
    (A : ι → Matrix D D ℂ) (z : ℂ) : Matrix D D ℂ :=
  wordMatrixVacuumCompression (resolvent (wordNativeMatrixLinearCombination A₀ A) z)

open scoped Matrix.Norms.L2Operator in
/-- The native compressed free resolvent has a reciprocal-height norm bound independent of the deterministic mean. -/
theorem specNorm_wordNativeDysonResolvent_le
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    {A : ι → Matrix D D ℂ} (hA : ∀ i, (A i).IsHermitian)
    {z : ℂ} (hz : z.im≠0) :
    specNorm (wordNativeDysonResolvent A₀ A z)≤(Fintype.card D : ℝ)*|z.im|⁻¹ := by
  exact (specNorm_wordMatrixVacuumCompression_le _).trans
    (mul_le_mul_of_nonneg_left
      ((isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA).norm_resolvent_le hz)
      (Nat.cast_nonneg _))

/-- The actual compressed free resolvent satisfies the native Dyson equation at every nonreal parameter. -/
theorem wordNativeDysonResolvent_dyson
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    {A : ι → Matrix D D ℂ} (hA : ∀ i, (A i).IsHermitian)
    {z : ℂ} (hz : z.im≠0) :
    (z•(1 : Matrix D D ℂ)-A₀-
      ∑ i, A i*wordNativeDysonResolvent A₀ A z*A i)*wordNativeDysonResolvent A₀ A z=1 := by
  exact wordMatrixVacuumCompression_resolvent_dyson A₀ A
    ((isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA).isUnit_algebraMap_sub_of_im_ne_zero hz)

open scoped Matrix.Norms.L2Operator in
/-- The nonreal derivative of the genuine compressed free resolvent is its compressed negative square. -/
theorem hasDerivAt_wordNativeDysonResolvent
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    {A : ι → Matrix D D ℂ} (hA : ∀ i, (A i).IsHermitian)
    {z : ℂ} (hz : z.im≠0) :
    HasDerivAt (wordNativeDysonResolvent A₀ A)
      (wordMatrixVacuumCompression
        (-(resolvent (wordNativeMatrixLinearCombination A₀ A) z)^2)) z := by
  have hr := spectrum.hasDerivAt_resolvent_const_left
    ((isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA).isUnit_algebraMap_sub_of_im_ne_zero hz)
  exact (wordMatrixVacuumCompressionCLM (D := D) (ι := ι)).hasFDerivAt.comp_hasDerivAt z hr

open scoped Matrix.Norms.L2Operator in
/-- The actual native compressed free resolvent is differentiable off the real axis. -/
theorem differentiableOn_wordNativeDysonResolvent
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    {A : ι → Matrix D D ℂ} (hA : ∀ i, (A i).IsHermitian) :
    DifferentiableOn ℂ (wordNativeDysonResolvent A₀ A) {z : ℂ | z.im≠0} := by
  intro z hz
  exact (hasDerivAt_wordNativeDysonResolvent hA₀ hA hz).differentiableAt.differentiableWithinAt

open scoped Matrix.Norms.L2Operator in
/-- The actual native compressed free resolvent is holomorphic off the real axis. -/
theorem analyticOnNhd_wordNativeDysonResolvent
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    {A : ι → Matrix D D ℂ} (hA : ∀ i, (A i).IsHermitian) :
    AnalyticOnNhd ℂ (wordNativeDysonResolvent A₀ A) {z : ℂ | z.im≠0} := by
  exact (Complex.analyticOnNhd_iff_differentiableOn
    (isOpen_ne_fun Complex.continuous_im continuous_const)).mpr
      (differentiableOn_wordNativeDysonResolvent hA₀ hA)

open scoped Matrix in
/-- The actual native free resolvent compression respects Schwarz reflection. -/
theorem wordNativeDysonResolvent_star
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    {A : ι → Matrix D D ℂ} (hA : ∀ i, (A i).IsHermitian) (z : ℂ) :
    wordNativeDysonResolvent A₀ A (star z)=(wordNativeDysonResolvent A₀ A z)ᴴ := by
  have hself := (isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA).star_eq
  have hr := star_resolvent (wordNativeMatrixLinearCombination A₀ A) z
  rw [hself] at hr
  unfold wordNativeDysonResolvent
  rw [← hr]
  ext i j
  simp only [wordMatrixVacuumCompression_apply,CStarMatrix.star_apply,
    wordVacuumExpectation_star,Matrix.conjTranspose_apply]

end NLAlib
