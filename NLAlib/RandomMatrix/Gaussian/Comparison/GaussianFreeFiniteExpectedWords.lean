import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteSymmetries
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteResolventWords
import NLAlib.Matrix.Structured.EnsembleEntryInvariants
import NLAlib.ForMathlib.Algebra.ResolventHom
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual finite-N expected resolvent-word tensor symmetry

The signed-permutation symmetries of the genuine Gaussian coordinate model
are transported through actual algebraic resolvents and Bochner integration.
Consequently the actual expected word is a tensor with the ensemble identity.
No invariant-expectation or scalar-block certificate is assumed.
Source: arXiv:2108.06312v2, Lemma 5.2 and Corollary 5.3.
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

private def ensembleReflectionUnitary (t : n) : Matrix.unitaryGroup (d × n) ℂ :=
  ⟨Matrix.diagonal (fun ab : d × n => if ab.2=t then (-1 : ℂ) else 1),by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change Matrix.diagonal _*(Matrix.diagonal _)ᴴ=1
    rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    ext ab ce
    by_cases h : ab=ce
    · subst ce
      by_cases ht : ab.2=t <;> simp [ht]
    · simp [h]⟩

private def ensembleReflectionAut (t : n) : M ≃ₐ[ℂ] M :=
  (Unitary.conjStarAlgAut ℂ M (ensembleReflectionUnitary (d := d) t)).toAlgEquiv

private theorem ensembleReflectionAut_apply (t : n) (T : M) (ab ce : d × n) :
    ensembleReflectionAut t T ab ce =
      (if ab.2=t then (-1 : ℂ) else 1)*T ab ce*(if ce.2=t then (-1 : ℂ) else 1) := by
  by_cases ha : ab.2=t <;> by_cases hc : ce.2=t
  all_goals simp [ensembleReflectionAut,Unitary.conjStarAlgAut_apply,ensembleReflectionUnitary,
    Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul,Matrix.mul_diagonal,ha,hc]

private def ensemblePermutationAut (σ : Equiv.Perm n) : M ≃ₐ[ℂ] M :=
  Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodCongr (Equiv.refl d) σ.symm)

private theorem ensemblePermutationAut_apply (σ : Equiv.Perm n) (T : M) (ab ce : d × n) :
    ensemblePermutationAut σ T ab ce = T (ab.1,σ ab.2) (ce.1,σ ce.2) := by
  rfl

private theorem map_finite_resolvent_word (φ : M →ₐ[ℂ] M) (T : M)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, ζ j ∈ resolventSet ℂ T) :
    φ ((List.ofFn (fun j => resolvent T (ζ j))).prod) =
      (List.ofFn (fun j => resolvent (φ T) (ζ j))).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.ofFn_succ,List.prod_cons,map_mul,φ.map_resolvent (hζ 0)]
    exact congrArg (fun U => resolvent (φ T) (ζ 0)*U)
      (ih (fun j => ζ j.succ) (fun j => hζ j.succ))

open scoped Matrix.Norms.L2Operator in
private theorem finite_word_transport
    (φ : M ≃ₐ[ℂ] M) (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0)
    (S : E → E) (hS : ∀ x, gaussianFreeFiniteInterpolation A₀ A q (S x) =
      φ (gaussianFreeFiniteInterpolation A₀ A q x)) (x : E) :
    gaussianFreeFiniteResolventWord A₀ A q ζ (S x) =
      φ (gaussianFreeFiniteResolventWord A₀ A q ζ x) := by
  unfold gaussianFreeFiniteResolventWord
  rw [hS]
  symm
  apply map_finite_resolvent_word φ.toAlgHom _ ζ
  intro j
  change IsUnit (algebraMap ℂ M (ζ j)-gaussianFreeFiniteInterpolation A₀ A q x)
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x).isUnit_smul_one_sub_of_im_ne_zero (hζ j)

open scoped Matrix.Norms.L2Operator in
private theorem expected_word_transport
    (φ : M ≃ₐ[ℂ] M) (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0)
    (S : E → E) (hμ : MeasurePreserving S
      (gaussianVector (GaussianFreeFiniteCoordinate ι n))
      (gaussianVector (GaussianFreeFiniteCoordinate ι n)))
    (hS : ∀ x, gaussianFreeFiniteInterpolation A₀ A q (S x) =
      φ (gaussianFreeFiniteInterpolation A₀ A q x)) :
    (∫ x : E, gaussianFreeFiniteResolventWord A₀ A q ζ x
      ∂gaussianVector (GaussianFreeFiniteCoordinate ι n)) =
      φ (∫ x : E, gaussianFreeFiniteResolventWord A₀ A q ζ x
        ∂gaussianVector (GaussianFreeFiniteCoordinate ι n)) := by
  let μ := gaussianVector (GaussianFreeFiniteCoordinate ι n)
  let F : E → M := gaussianFreeFiniteResolventWord A₀ A q ζ
  let L : M →L[ℂ] M := φ.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hF : Integrable F μ := integrable_gaussianFreeFiniteResolventWord A₀ hA₀ A hA q ζ hζ
  have hFc : Continuous F :=
    (contDiff_gaussianFreeFiniteResolventWord A₀ hA₀ A hA q ζ hζ (r := 0)).continuous
  change (∫ x, F x ∂μ)=φ (∫ x, F x ∂μ)
  calc
    _ = ∫ x, F (S x) ∂μ := by
      have he := integral_map hμ.aemeasurable hFc.aestronglyMeasurable
      rw [hμ.map_eq] at he
      exact he
    _ = ∫ x, L (F x) ∂μ := integral_congr_ae (Filter.Eventually.of_forall fun x =>
      finite_word_transport φ A₀ hA₀ A hA q ζ hζ S hS x)
    _ = _ := L.integral_comp_comm hF

open scoped Matrix.Norms.L2Operator in
/-- The actual expected nonreal finite-N resolvent word is a tensor with
the ensemble identity. Both expectation invariance and integrability are
proved from the actual independent coordinate model. Empty dimension and
zero word length are included.
Source: arXiv:2108.06312v2, Lemma 5.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem exists_integral_gaussianFreeFiniteResolventWord_eq_kronecker_one
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0) :
    ∃ Q : Matrix d d ℂ,
      (∫ x : E, gaussianFreeFiniteResolventWord A₀ A q ζ x
        ∂gaussianVector (GaussianFreeFiniteCoordinate ι n)) = Q⊗ₖ(1 : Matrix n n ℂ) := by
  apply exists_eq_kronecker_one_of_ensemble_entry_invariant
  · intro σ a b r s
    have h := expected_word_transport (ensemblePermutationAut (d := d) σ)
      A₀ hA₀ A hA q ζ hζ
      (fun x k => x (gaussianFreeEnsembleCoordinatePerm σ k))
      (measurePreserving_gaussianFreeEnsemble_permute σ)
      (fun x => gaussianFreeFiniteInterpolation_permute A₀ A q x σ)
    have he := congrFun (congrFun h (a,r)) (b,s)
    simpa only [ensemblePermutationAut_apply] using he.symm
  · intro t a b r s
    have h := expected_word_transport (ensembleReflectionAut (d := d) t)
      A₀ hA₀ A hA q ζ hζ (gaussianFreeEnsembleReflect t)
      (measurePreserving_gaussianFreeEnsemble_reflect t) (fun x => by
        ext ab ce
        rw [ensembleReflectionAut_apply]
        exact congrFun (congrFun (gaussianFreeFiniteInterpolation_reflect A₀ A q x t) ab) ce)
    have he := congrFun (congrFun h (a,r)) (b,s)
    simpa only [ensembleReflectionAut_apply] using he

open scoped Matrix.Norms.L2Operator in
/-- The two genuine finite-N covariance families cancel on the actual
expected resolvent word. The scalar tensor structure is proved, rather than
supplied as a cancellation premise.
Source: arXiv:2108.06312v2, Corollary 5.3 and Lemma 6.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem sum_diagonal_sub_gue_covariance_sandwich_integral_resolvent_word
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0) :
    let W := ∫ x : E, gaussianFreeFiniteResolventWord A₀ A q ζ x
      ∂gaussianVector (GaussianFreeFiniteCoordinate ι n)
    (∑ i, ∑ a : n, (A i⊗ₖ(Matrix.single a a 1 : Matrix n n ℂ))*W*
      (A i⊗ₖ(Matrix.single a a 1 : Matrix n n ℂ))) -
    (∑ i, ∑ k : GUECoordinate Unit n, (A i⊗ₖgueCoefficientMatrix k)*W*
      (A i⊗ₖgueCoefficientMatrix k)) = 0 := by
  dsimp only
  obtain ⟨Q,hQ⟩ := exists_integral_gaussianFreeFiniteResolventWord_eq_kronecker_one (n := n)
    A₀ hA₀ A hA q ζ hζ
  rw [hQ]
  exact sum_diagonal_sub_gue_covariance_sandwich_identity A Q

end NLAlib

end
