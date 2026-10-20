import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteResolventStein
import NLAlib.Matrix.Functions.MixedResolventDerivatives
import NLAlib.Matrix.Functions.ResolventWordDerivativeBounds

/-! # Genuine native mixed arcs for the Gaussian covariance identity

The functions here are literal mixed powers of the actual source random
matrix. Their smoothness, uniform first-derivative domination, and positive
arc insertion formula are derived before applying Gaussian covariance.
Source: arXiv:2108.06312v2, Lemma 6.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ
local notation "J" => (((d × n) × (d × n)) ⊕ ((d × n) × (d × n))) → ℝ
local notation "H" => (hermitianMatrixFromRealCoordinates : J →L[ℝ] M)

/-- A literal positive or zero mixed resolvent arc of the genuine finite-N
Gaussian matrix; all inverse factors use the same actual sample matrix. -/
def gaussianFreeFiniteMixedArc (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (q : ℝ) (ζ : ℂ) (a b : ℕ) (x : E) : M :=
  resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ ^ a *
    resolvent (gaussianFreeFiniteInterpolation A₀ A q x) (star ζ) ^ b

private def mixedArcBlocks (ζ : ℂ) (a b : ℕ) : Fin (a + b) → ℂ × M :=
  Fin.append (fun _ : Fin a => (ζ, 1)) (fun _ : Fin b => (star ζ, 1))

omit [Fintype n] [Fintype d] in
private theorem mixedArcBlocks_im (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b : ℕ) :
    ∀ j, ((mixedArcBlocks (n := n) (d := d) ζ a b) j).1.im ≠ 0 := by
  intro j
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j
  · simpa only [mixedArcBlocks, Fin.append_left] using hζ
  · simpa only [mixedArcBlocks, Fin.append_right, Complex.star_def,
      Complex.conj_im] using neg_ne_zero.mpr hζ

omit [Fintype n] [Fintype d] in
private theorem mixedArcBlocks_height (ζ : ℂ) (a b : ℕ) :
    ∀ j, |((mixedArcBlocks (n := n) (d := d) ζ a b) j).1.im|⁻¹ = |ζ.im|⁻¹ := by
  intro j
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j
  · simp only [mixedArcBlocks, Fin.append_left]
  · simp only [mixedArcBlocks, Fin.append_right, Complex.star_def,
      Complex.conj_im, abs_neg]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- Every actual native mixed arc is globally smooth on the complete real
Gaussian coordinate space, including zero exponents and empty dimensions. -/
theorem contDiff_gaussianFreeFiniteMixedArc
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b : ℕ) {r : WithTop ℕ∞} :
    ContDiff ℝ r (gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ a b) := by
  have hr (ω : ℂ) (hω : ω.im ≠ 0) : ContDiff ℝ r
      (fun x : E => resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ω) := by
    have heq : (fun x : E => resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ω) =
        gaussianFreeFiniteResolventWord A₀ A q (fun _ : Fin 1 => ω) := by
      funext x
      simp [gaussianFreeFiniteResolventWord]
    rw [heq]
    exact contDiff_gaussianFreeFiniteResolventWord (n := n) A₀ hA₀ A hA q
      (fun _ : Fin 1 => ω) (fun _ => hω) (r := r)
  exact ((hr ζ hζ).pow a).mul ((hr (star ζ)
    (by simpa only [Complex.star_def, Complex.conj_im] using neg_ne_zero.mpr hζ)).pow b)

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual arc and its actual first derivative admit global uniform
bounds. The constants are constructed from the native coefficient maps and
nonreal height; no regularity or domination premise is assumed. -/
theorem exists_uniform_bounds_gaussianFreeFiniteMixedArc
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b : ℕ) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (∀ x : E, specNorm (gaussianFreeFiniteMixedArc A₀ A q ζ a b x) ≤ C₀) ∧
      ∀ x : E, ‖fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ a b) x‖ ≤ C₁ := by
  let A₀N : M := A₀ ⊗ₖ (1 : Matrix n n ℂ)
  have hA₀N : A₀N.IsHermitian := by
    change (A₀ ⊗ₖ (1 : Matrix n n ℂ))ᴴ = A₀ ⊗ₖ (1 : Matrix n n ℂ)
    rw [Matrix.conjTranspose_kronecker, hA₀.eq, Matrix.conjTranspose_one]
  let L := gaussianFreeFiniteSeriesCLM (n := n) A q
  let D : E →L[ℝ] J := matrixRealCoordinatesContinuousLinearEquiv.toContinuousLinearMap.comp L
  let w := mixedArcBlocks (n := n) (d := d) ζ a b
  let g : J → M := hermitianCoordinateResolventWord A₀N w
  have hw : ∀ j, (w j).1.im ≠ 0 := mixedArcBlocks_im ζ hζ a b
  have hg : ContDiff ℝ ⊤ g := contDiff_hermitianCoordinateResolventWord A₀N hA₀N w hw
  have hrec (x : E) : H (D x) = L x := by
    change H (matrixRealCoordinates (L x)) = L x
    apply hermitianMatrixFromRealCoordinates_matrixRealCoordinates
    simpa only [L, gaussianFreeFiniteSeriesCLM_apply] using
      isHermitian_sum_smul_real _ (gaussianFreeFiniteCoefficient_isHermitian A hA q) x
  have heq : gaussianFreeFiniteMixedArc A₀ A q ζ a b = g ∘ D := by
    funext x
    simp only [g, Function.comp_apply, hermitianCoordinateResolventWord,
      hermitianCoordinateResolvent, hrec, w, mixedArcBlocks, List.ofFn_fin_append,
      List.map_append, List.prod_append, List.ofFn_const, List.map_replicate,
      List.prod_replicate, mul_one]
    simp only [gaussianFreeFiniteMixedArc, gaussianFreeFiniteInterpolation,
      A₀N, L, gaussianFreeFiniteSeriesCLM_apply]
  let c : ℝ := |ζ.im|⁻¹
  let P : ℝ := ∏ j, ‖(w j).2‖
  let C₀ : ℝ := c ^ (a + b) * P
  let C₁ : ℝ := (a + b : ℕ) * c ^ (a + b + 1) * P * ‖H‖ * ‖D‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hP : 0 ≤ P := Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine ⟨C₀, C₁, by dsimp [C₀]; positivity, by dsimp [C₁]; positivity, ?_, ?_⟩
  · intro x
    rw [heq]
    simpa only [Function.comp_apply, specNorm_eq_norm, g, C₀, P] using
      norm_hermitianCoordinateResolventWord_le A₀N hA₀N w hw hc
        (fun j => (mixedArcBlocks_height ζ a b j).le) (D x)
  · intro x
    rw [heq, (hg.differentiable (by simp) (D x)).hasFDerivAt.comp x D.hasFDerivAt |>.fderiv]
    calc
      _ ≤ ‖fderiv ℝ g (D x)‖ * ‖D‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C₁ := mul_le_mul_of_nonneg_right
        (norm_fderiv_hermitianCoordinateResolventWord_le A₀N hA₀N w hw hc
          (fun j => (mixedArcBlocks_height ζ a b j).le) (D x)) (norm_nonneg _)

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
set_option maxHeartbeats 800000 in
/-- Exact positive-arc insertion formula for the genuine native mixed arc's
coordinate derivative. Inserted coefficients need not commute with the
resolvents; zero arc exponents simply contribute empty sums.
Source: arXiv:2108.06312v2, Lemma 6.3.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem fderiv_gaussianFreeFiniteMixedArc_apply
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b : ℕ) (x h : E) :
    let R := resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ
    let S := resolvent (gaussianFreeFiniteInterpolation A₀ A q x) (star ζ)
    let V := ∑ k, h k • gaussianFreeFiniteCoefficient A q k
    fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ a b) x h =
      (∑ i ∈ Finset.range a, R ^ (a - i) * V * R ^ (i + 1) * S ^ b) +
      ∑ j ∈ Finset.range b, R ^ a * S ^ (b - j) * V * S ^ (j + 1) := by
  let l : ℝ → E := fun t => x + t • h
  have hl : HasDerivAt l h 0 := by simpa [l] using (hasDerivAt_id (0 : ℝ)).smul_const h |>.const_add x
  have hcurve (ω : ℂ) (hω : ω.im ≠ 0) : HasDerivAt
      (fun t : ℝ => resolvent (gaussianFreeFiniteInterpolation A₀ A q (l t)) ω)
      (resolvent (gaussianFreeFiniteInterpolation A₀ A q (l 0)) ω *
        (∑ k, h k • gaussianFreeFiniteCoefficient A q k) *
        resolvent (gaussianFreeFiniteInterpolation A₀ A q (l 0)) ω) 0 := by
    have hc : ContDiff ℝ ⊤
        (fun y : E => resolvent (gaussianFreeFiniteInterpolation A₀ A q y) ω) := by
      have heq : (fun y : E => resolvent (gaussianFreeFiniteInterpolation A₀ A q y) ω) =
          gaussianFreeFiniteResolventWord A₀ A q (fun _ : Fin 1 => ω) := by
        funext y
        simp [gaussianFreeFiniteResolventWord]
      rw [heq]
      exact contDiff_gaussianFreeFiniteResolventWord (n := n) A₀ hA₀ A hA q
        (fun _ : Fin 1 => ω) (fun _ => hω) (r := ⊤)
    have hd := (hc.differentiable (by simp) (l 0)).hasFDerivAt.comp_hasDerivAt 0 hl
    simpa only [l, zero_smul, add_zero, Function.comp_def,
      fderiv_gaussianFreeFiniteResolvent_apply A₀ hA₀ A hA q ω hω] using hd
  have hd := hasDerivAt_mixed_powers_of_sandwich
    (R := fun t : ℝ => resolvent (gaussianFreeFiniteInterpolation A₀ A q (l t)) ζ)
    (S := fun t : ℝ => resolvent (gaussianFreeFiniteInterpolation A₀ A q (l t)) (star ζ))
    (t := (0 : ℝ))
    (∑ k, h k • gaussianFreeFiniteCoefficient A q k) (hcurve ζ hζ)
    (hcurve (star ζ) (by simpa only [Complex.star_def, Complex.conj_im] using neg_ne_zero.mpr hζ)) a b
  have hf : HasDerivAt (fun t : ℝ => gaussianFreeFiniteMixedArc A₀ A q ζ a b (l t))
      (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ a b) x h) 0 := by
    have hc := ((contDiff_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ a b
      (r := ⊤)).differentiable (by simp) (l 0)).hasFDerivAt.comp_hasDerivAt 0 hl
    simpa only [l, Function.comp_def, zero_smul, add_zero] using hc
  apply hf.unique
  simpa only [gaussianFreeFiniteMixedArc, l, Function.comp_def,
    Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero] using hd

end NLAlib
