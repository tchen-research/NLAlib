import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteExpectedWords
import NLAlib.Probability.Gaussian.Calculus.CoordinateSplitInterpolation
import NLAlib.Matrix.Functions.ResolventMomentDerivativeBounds

/-! # Actual finite-N resolvent variance derivative

The exact covariance interpolation is instantiated with the true matrix
coefficient realization. Global C² regularity and domination are derived
from the actual nonreal resolvent word, including arbitrary mean and empty
dimensions. Source: arXiv:2108.06312v2, Lemmas 4.11 and 6.2.
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

private def finiteBaseCoefficient (A : ι → Matrix d d ℂ) : K → M
  | .inl ia => A ia.1⊗ₖ(Matrix.single ia.2 ia.2 1 : Matrix n n ℂ)
  | .inr ik => A ik.1⊗ₖgueCoefficientMatrix ik.2

omit [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d] in
private theorem finiteBaseCoefficient_isHermitian
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (k : K) :
    (finiteBaseCoefficient A k).IsHermitian := by
  cases k with
  | inl ia => simpa [finiteBaseCoefficient,gaussianFreeFiniteCoefficient] using
      gaussianFreeFiniteCoefficient_isHermitian A hA 1 (.inl ia)
  | inr ik => simpa [finiteBaseCoefficient,gaussianFreeFiniteCoefficient] using
      gaussianFreeFiniteCoefficient_isHermitian A hA 0 (.inr ik)

open scoped Matrix.Norms.L2Operator in
private def finiteBaseSeries (A : ι → Matrix d d ℂ) : E →L[ℝ] M :=
  ∑ k, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : K => ℝ) k).smulRight
    (finiteBaseCoefficient A k)

omit [Fintype d] [DecidableEq ι] [DecidableEq d] in
open scoped Matrix.Norms.L2Operator in
private theorem finiteBaseSeries_apply (A : ι → Matrix d d ℂ) (x : E) :
    finiteBaseSeries A x = ∑ k, x k • finiteBaseCoefficient A k := by
  simp [finiteBaseSeries]

open scoped Matrix.Norms.L2Operator in
private def finiteBaseCoordinates (A : ι → Matrix d d ℂ) : E →L[ℝ] J :=
  matrixRealCoordinatesContinuousLinearEquiv.toContinuousLinearMap.comp (finiteBaseSeries A)

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem reconstruct_finiteBaseCoordinates
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (x : E) :
    H (finiteBaseCoordinates A x) = ∑ k, x k • finiteBaseCoefficient A k := by
  change H (matrixRealCoordinates (finiteBaseSeries A x)) = _
  rw [finiteBaseSeries_apply]
  exact hermitianMatrixFromRealCoordinates_matrixRealCoordinates
    (isHermitian_sum_smul_real _ (finiteBaseCoefficient_isHermitian A hA) x)

open scoped Matrix.Norms.L2Operator in
private theorem reconstruct_finiteBaseCoordinates_single
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (k : K) :
    H (finiteBaseCoordinates A (Pi.single k 1)) = finiteBaseCoefficient A k := by
  rw [reconstruct_finiteBaseCoordinates A hA]
  simp

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem reconstruct_finiteBaseCoordinates_split
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (q : ℝ) (x : E) :
    A₀⊗ₖ(1 : Matrix n n ℂ)+H (finiteBaseCoordinates A (gaussianCoordinateSplit q x)) =
      gaussianFreeFiniteInterpolation A₀ A q x := by
  rw [reconstruct_finiteBaseCoordinates A hA]
  unfold gaussianFreeFiniteInterpolation
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  cases k <;> simp [gaussianCoordinateSplit,finiteBaseCoefficient,
    gaussianFreeFiniteCoefficient,smul_smul,mul_comm]

/-- A genuine finite-N resolvent word with fixed matrices between its
ordered nonreal inverse factors. Inserted words use the same actual random
matrix at every factor. -/
def gaussianFreeFiniteBlockWord (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (q : ℝ) {m : ℕ} (w : Fin m → ℂ×M) (x : E) : M :=
  ((List.ofFn w).map (fun b => resolvent (gaussianFreeFiniteInterpolation A₀ A q x)
    b.1*b.2)).prod

open scoped Matrix.Norms.L2Operator in
private theorem coordinate_word_split_eq
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (q : ℝ) {m : ℕ}
    (w : Fin m → ℂ×M) (x : E) :
    hermitianCoordinateResolventWord (A₀⊗ₖ(1 : Matrix n n ℂ)) w
      (finiteBaseCoordinates A (gaussianCoordinateSplit q x)) =
        gaussianFreeFiniteBlockWord A₀ A q w x := by
  unfold hermitianCoordinateResolventWord gaussianFreeFiniteBlockWord
  simp_rw [hermitianCoordinateResolvent,reconstruct_finiteBaseCoordinates_split A₀ A hA]

open scoped Matrix.Norms.L2Operator in
/-- The genuine finite-N mixed resolvent trace has the exact diagonal-minus-
GUE covariance derivative. Every term is an actual twice-inserted resolvent
word under the canonical Gaussian coordinate law. No regularity, Gaussian
law, covariance, or derivative formula is assumed.
Source: arXiv:2108.06312v2, Lemmas 4.11 and 6.2, before the cyclic regrouping.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem hasDerivAt_integral_normalizedTrace_gaussianFreeFinite_mixed_resolvent
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im≠0) (p : ℕ) {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    let w := mixedResolventWord (n := d×n) ζ p
    HasDerivAt
      (fun t : ℝ => ∫ x : E, normalizedTrace
        (resolvent (gaussianFreeFiniteInterpolation A₀ A t x) ζ ^ p *
          resolvent (gaussianFreeFiniteInterpolation A₀ A t x) (star ζ) ^ p)
        ∂gaussianVector K)
      ((1/2 : ℝ) •
        ((∑ i, ∑ a : n, ∫ x : E, ∑ j : Fin (p+p), ∑ k : Fin (p+p+1),
          normalizedTrace (gaussianFreeFiniteBlockWord A₀ A q
            (resolventWordInsert (resolventWordInsert w j
              (A i⊗ₖ(Matrix.single a a 1 : Matrix n n ℂ))) k
              (A i⊗ₖ(Matrix.single a a 1 : Matrix n n ℂ))) x) ∂gaussianVector K)-
         (∑ i, ∑ a : GUECoordinate Unit n, ∫ x : E,
          ∑ j : Fin (p+p), ∑ k : Fin (p+p+1),
          normalizedTrace (gaussianFreeFiniteBlockWord A₀ A q
            (resolventWordInsert (resolventWordInsert w j
              (A i⊗ₖgueCoefficientMatrix a)) k (A i⊗ₖgueCoefficientMatrix a)) x)
          ∂gaussianVector K))) q := by
  dsimp only
  let A₀N : M := A₀⊗ₖ(1 : Matrix n n ℂ)
  have hA₀N : A₀N.IsHermitian := by
    change (A₀⊗ₖ(1 : Matrix n n ℂ))ᴴ=A₀⊗ₖ(1 : Matrix n n ℂ)
    rw [Matrix.conjTranspose_kronecker,hA₀.eq,Matrix.conjTranspose_one]
  let D : E →L[ℝ] J := finiteBaseCoordinates A
  let g : J → ℂ := fun y => normalizedTrace
    (resolvent (A₀N+H y) ζ ^ p*resolvent (A₀N+H y) (star ζ) ^ p)
  let f : E → ℂ := g ∘ D
  let df := fderiv ℝ f
  let ddf := fderiv ℝ df
  have hc : ContDiff ℝ ⊤ g :=
    contDiff_normalizedTrace_mixed_resolvent_coordinate A₀N hA₀N ζ hζ p
  have hfc : ContDiff ℝ ⊤ f := hc.comp D.contDiff
  have hdfc : ContDiff ℝ ⊤ df := hfc.fderiv_right (by simp)
  have hddfc : ContDiff ℝ ⊤ ddf := hdfc.fderiv_right (by simp)
  let C₀ : ℝ := |ζ.im|⁻¹ ^ (2*p)
  let C₁ : ℝ := ((2*p : ℕ) : ℝ)*|ζ.im|⁻¹^(2*p+1)*‖H‖
  let C₂ : ℝ := ((2*p : ℕ) : ℝ)*((2*p+1 : ℕ) : ℝ)*|ζ.im|⁻¹^(2*p+2)*‖H‖^2
  have hfb (x : E) : ‖f x‖≤C₀ :=
    norm_normalizedTrace_mixed_resolvent_coordinate_le A₀N hA₀N ζ hζ p (D x)
  have hdfb (x : E) : ‖df x‖≤C₁*‖D‖ := by
    change ‖fderiv ℝ (g ∘ D) x‖≤_
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), D.iteratedFDeriv_comp_right hc x (by simp)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 1 g (D x)‖*∏ _ : Fin 1, ‖D‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ C₁*‖D‖ := by
        simp only [norm_iteratedFDeriv_one,Fin.prod_univ_one]
        exact mul_le_mul_of_nonneg_right
          (norm_fderiv_normalizedTrace_mixed_resolvent_coordinate_le A₀N hA₀N ζ hζ p (D x))
          (norm_nonneg _)
  have hddfb (x : E) : ‖ddf x‖≤C₂*‖D‖^2 := by
    change ‖fderiv ℝ (fderiv ℝ (g ∘ D)) x‖≤_
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ),norm_iteratedFDeriv_fderiv,
      D.iteratedFDeriv_comp_right hc x (by simp)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 2 g (D x)‖*∏ _ : Fin 2, ‖D‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ C₂*‖D‖^2 := by
        simp only [Fin.prod_univ_two,← sq]
        exact mul_le_mul_of_nonneg_right
          (norm_iteratedFDeriv_two_normalizedTrace_mixed_resolvent_coordinate_le
            A₀N hA₀N ζ hζ p (D x)) (sq_nonneg _)
  have hd := hasDerivAt_integral_gaussianCoordinateSplit f df ddf
    (fun x => (hfc.differentiable (by simp) x).hasFDerivAt)
    (fun x => (hdfc.differentiable (by simp) x).hasFDerivAt)
    hddfc.continuous C₀ (C₁*‖D‖) (C₂*‖D‖^2) hfb hdfb hddfb hq hq1
  have hfunction (t : ℝ) (x : E) : f (gaussianCoordinateSplit t x) = normalizedTrace
      (resolvent (gaussianFreeFiniteInterpolation A₀ A t x) ζ ^ p*
        resolvent (gaussianFreeFiniteInterpolation A₀ A t x) (star ζ) ^ p) := by
    dsimp only [f,Function.comp_def,g,D,A₀N]
    rw [reconstruct_finiteBaseCoordinates_split A₀ A hA]
  simp_rw [hfunction] at hd
  have hh (k : K) (x : E) : ddf (gaussianCoordinateSplit q x)
      (Pi.single k 1) (Pi.single k 1) =
      ∑ j : Fin (p+p), ∑ l : Fin (p+p+1),
        normalizedTrace (gaussianFreeFiniteBlockWord A₀ A q
          (resolventWordInsert (resolventWordInsert (mixedResolventWord ζ p) j
            (finiteBaseCoefficient A k)) l (finiteBaseCoefficient A k)) x) := by
    let u : E := Pi.single k (1 : ℝ)
    change fderiv ℝ (fderiv ℝ f) (gaussianCoordinateSplit q x) u u = _
    have ht := iteratedFDeriv_two_apply (𝕜 := ℝ) f (gaussianCoordinateSplit q x) ![u,u]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at ht
    rw [← ht]
    rw [D.iteratedFDeriv_comp_right hc _ (by simp)]
    let T : M →L[ℝ] ℂ :=
      (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ
    have hgeq : g = T ∘ hermitianCoordinateResolventWord A₀N (mixedResolventWord ζ p) := by
      funext y
      simp [g,T,hermitianCoordinateResolventWord_mixed]
    rw [hgeq,T.iteratedFDeriv_comp_left
      (contDiff_hermitianCoordinateResolventWord A₀N hA₀N (mixedResolventWord ζ p)
        (im_ne_zero_mixedResolventWord ζ hζ p) (r := ⊤)).contDiffAt (by simp)]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe,Function.comp_apply]
    rw [iteratedFDeriv_two_hermitianCoordinateResolventWord_apply A₀N hA₀N
      (mixedResolventWord ζ p) (im_ne_zero_mixedResolventWord ζ hζ p)]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,map_sum,T,
      ContinuousLinearMap.coe_restrictScalars',LinearMap.coe_toContinuousLinearMap',
      normalizedTraceLinearMap_apply]
    dsimp only [u,D,A₀N]
    simp_rw [reconstruct_finiteBaseCoordinates_single A hA,
      coordinate_word_split_eq A₀ A hA]
  simp_rw [hh] at hd
  simpa only [Fintype.sum_prod_type,finiteBaseCoefficient] using hd

end NLAlib
