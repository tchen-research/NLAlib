import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteInterpolation
import NLAlib.Matrix.Functions.ResolventWordDerivativeBounds

/-!
# Actual finite-N resolvent-word regularity

The source interpolating matrix is genuinely Hermitian for every coordinate
input. Every nonreal scalar shift is therefore a unit. Its actual matrix
resolvent words are smooth, uniformly bounded, and Bochner integrable under
the canonical Gaussian product law.
Source: arXiv:2108.06312v2, Sections 5.1 and 6.1.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker

namespace NLAlib

variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]
local notation "E" => GaussianFreeFiniteCoordinate ι n → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ

/-- The literal ordered product of actual finite-N native resolvents. -/
def gaussianFreeFiniteResolventWord (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (q : ℝ) {m : ℕ} (ζ : Fin m → ℂ) (x : E) : M :=
  (List.ofFn (fun j => resolvent (gaussianFreeFiniteInterpolation A₀ A q x) (ζ j))).prod

open scoped Matrix.Norms.L2Operator in
private theorem contDiff_gaussianFreeFiniteResolvent
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun x : E => resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let L := gaussianFreeFiniteSeriesCLM (n := n) A q
  have hu : IsUnit (ζ • (1 : M)-gaussianFreeFiniteInterpolation A₀ A q x) :=
    (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x).isUnit_smul_one_sub_of_im_ne_zero hζ
  have hi := contDiffAt_ringInverse (n := r) ℝ hu.unit
  rw [hu.unit_spec] at hi
  have hT : gaussianFreeFiniteInterpolation A₀ A q x =
      A₀⊗ₖ(1 : Matrix n n ℂ)+L x := by simp [gaussianFreeFiniteInterpolation,L]
  rw [hT] at hi
  have ha : ContDiffAt ℝ r
      (fun y : E => ζ • (1 : M)-(A₀⊗ₖ(1 : Matrix n n ℂ)+L y)) x :=
    contDiffAt_const.sub (contDiffAt_const.add L.contDiff.contDiffAt)
  convert! hi.comp x ha using 1
  funext y
  simp [resolvent,Algebra.algebraMap_eq_smul_one,gaussianFreeFiniteInterpolation,L]

open scoped Matrix.Norms.L2Operator in
/-- Actual nonreal resolvent words of the source interpolant are globally
smooth on the entire independent real coordinate space. -/
theorem contDiff_gaussianFreeFiniteResolventWord
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0) {r : WithTop ℕ∞} :
    ContDiff ℝ r (gaussianFreeFiniteResolventWord (n := n) A₀ A q ζ) := by
  induction m with
  | zero =>
    have he : gaussianFreeFiniteResolventWord (n := n) A₀ A q ζ = fun _ : E => (1 : M) := by
      funext x
      simp [gaussianFreeFiniteResolventWord]
    rw [he]
    exact contDiff_const
  | succ m ih =>
    have he : gaussianFreeFiniteResolventWord (n := n) A₀ A q ζ = fun x : E =>
        resolvent (gaussianFreeFiniteInterpolation A₀ A q x) (ζ 0)*
          gaussianFreeFiniteResolventWord A₀ A q (Fin.tail ζ) x := by
      funext x
      simp only [gaussianFreeFiniteResolventWord,List.ofFn_succ,List.prod_cons]
      rfl
    rw [he]
    exact (contDiff_gaussianFreeFiniteResolvent A₀ hA₀ A hA q (ζ 0) (hζ 0)).mul
      (ih (Fin.tail ζ) (fun j => hζ j.succ))

open scoped Matrix.Norms.L2Operator in
/-- The actual word is bounded by the exact product of reciprocal imaginary
heights. This includes zero word length and empty matrix dimension. -/
theorem norm_gaussianFreeFiniteResolventWord_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0) (x : E) :
    ‖gaussianFreeFiniteResolventWord A₀ A q ζ x‖ ≤ ∏ j, |(ζ j).im|⁻¹ := by
  induction m with
  | zero =>
    simpa only [gaussianFreeFiniteResolventWord,List.ofFn_zero,List.prod_nil,
      Fin.prod_univ_zero,← specNorm_eq_norm] using (specNorm_one_le (n := d × n) (𝕜 := ℂ))
  | succ m ih =>
    simp only [gaussianFreeFiniteResolventWord,List.ofFn_succ,List.prod_cons]
    change ‖resolvent (gaussianFreeFiniteInterpolation A₀ A q x) (ζ 0)*
      gaussianFreeFiniteResolventWord A₀ A q (Fin.tail ζ) x‖ ≤ _
    have hR : ‖resolvent (gaussianFreeFiniteInterpolation A₀ A q x) (ζ 0)‖ ≤
        |(ζ 0).im|⁻¹ := by
      simpa only [← specNorm_eq_norm] using
        (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x).specNorm_resolvent_le (hζ 0)
    calc
      _ ≤ ‖resolvent (gaussianFreeFiniteInterpolation A₀ A q x) (ζ 0)‖*
          ‖gaussianFreeFiniteResolventWord A₀ A q (Fin.tail ζ) x‖ := norm_mul_le _ _
      _ ≤ |(ζ 0).im|⁻¹*∏ j : Fin m, |(ζ j.succ).im|⁻¹ :=
        mul_le_mul hR (ih (Fin.tail ζ) (fun j => hζ j.succ)) (norm_nonneg _) (by positivity)
      _ = _ := by rw [Fin.prod_univ_succ]

open scoped Matrix.Norms.L2Operator in
/-- Actual native resolvent words are genuinely Bochner integrable under
the true finite-N Gaussian coordinate probability measure. -/
theorem integrable_gaussianFreeFiniteResolventWord
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0) :
    Integrable (gaussianFreeFiniteResolventWord (n := n) A₀ A q ζ)
      (gaussianVector (GaussianFreeFiniteCoordinate ι n)) := by
  refine Integrable.of_bound
    (contDiff_gaussianFreeFiniteResolventWord A₀ hA₀ A hA q ζ hζ
      (r := 0)).continuous.aestronglyMeasurable (∏ j, |(ζ j).im|⁻¹) ?_
  exact Filter.Eventually.of_forall (norm_gaussianFreeFiniteResolventWord_le A₀ hA₀ A hA q ζ hζ)

end NLAlib

end
