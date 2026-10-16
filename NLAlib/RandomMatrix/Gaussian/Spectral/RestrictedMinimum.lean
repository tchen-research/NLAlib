import NLAlib.Matrix.Norms.RestrictedMinimum
import NLAlib.Matrix.Spectral.Core
import NLAlib.Matrix.Norms.SpectralNormBounds
import NLAlib.Matrix.Norms.RankOneDifferences
import NLAlib.Probability.Gaussian.Basic.GaussianWidth
import NLAlib.Probability.Gaussian.Basic.StandardVector
import NLAlib.Probability.Gaussian.Comparison.GordonMinimax
import NLAlib.Probability.Gaussian.Moments.ExpectationNormDiff
import NLAlib.RandomMatrix.Gaussian.Basic.LinearForms
import NLAlib.RandomMatrix.Gaussian.Basic.RowSplitting
import NLAlib.RandomMatrix.Gaussian.Basic.LipschitzConcentration

/-!
# Gaussian restricted minimum controlled by Gaussian width

Gordon comparison on deterministic finite nets, followed by Gaussian
concentration, proves escape through a mesh for a nonempty compact part of
the unit sphere. Source: Tropp 2020, Theorem 6.8; supplied reroutes W5–W9.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace
namespace NLAlib

private theorem matrix_net_minimax_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : IsCompact T) (hne : T.Nonempty)
    (ε : ℝ) (U : Finset (EuclideanSpace ℝ (Fin n)))
    (V : Finset (EuclideanSpace ℝ (Fin m)))
    (hV : ∀ v ∈ V, ‖v‖ = 1)
    (hcov : ∀ x ∈ T, ∃ u ∈ U, ‖x-u‖ ≤ ε) :
    (⨅ u : U, ⨆ v : V, ∑ i, ∑ j, v.1 i * A i j * u.1 j)
      ≤ restrictedMinimum A T + ε * specNorm A := by
  let Φ := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A
  obtain ⟨x,hx,he⟩ := exists_norm_eq_restrictedMinimum A hT hne
  obtain ⟨u,hu,hxu⟩ := hcov x hx
  have h1 : (⨅ u : U, ⨆ v : V, ∑ i, ∑ j, v.1 i * A i j * u.1 j) ≤ ‖Φ u‖ := by
    refine (ciInf_le (Set.finite_range _).bddBelow ⟨u,hu⟩).trans ?_
    refine Real.iSup_le (fun v => ?_) (norm_nonneg _)
    rw [← inner_toEuclideanLin_eq_sum]
    exact (real_inner_le_norm _ _).trans (by rw [hV _ v.2, one_mul])
  have h2 : ‖Φ u‖ ≤ ‖Φ x‖ + specNorm A * ε := by
    have hd : Φ u = Φ x - Φ (x-u) := by rw [map_sub]; abel
    rw [hd]
    refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
    exact (Φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left hxu (norm_nonneg _))
  change ‖Φ x‖ = restrictedMinimum A T at he
  linarith

private theorem gaussian_net_minimax_ge {m n : ℕ} (hm : 0 < m)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : IsCompact T)
    (ε : ℝ) (U : Finset (EuclideanSpace ℝ (Fin n)))
    (V : Finset (EuclideanSpace ℝ (Fin m))) (hU : ↑U ⊆ T) [Nonempty U]
    (hcov : ∀ y : EuclideanSpace ℝ (Fin m), ‖y‖ = 1 → ∃ v ∈ V, ‖y-v‖ ≤ ε)
    (H : Matrix (Fin 1) (Fin (n+m)) ℝ) :
    (1-ε) * ‖(WithLp.toLp 2 (fun i => H 0 (Fin.natAdd n i)) : EuclideanSpace ℝ (Fin m))‖
      - realSupportFunction T (-WithLp.toLp 2 (fun j => H 0 (Fin.castAdd m j)))
      ≤ ⨅ u : U, ⨆ v : V,
        linForm (fun _ k => Fin.append (fun j => u.1 j) (fun i => v.1 i) k) H := by
  let h : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i => H 0 (Fin.natAdd n i))
  let g : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => H 0 (Fin.castAdd m j))
  obtain ⟨y,hy1,hyh⟩ : ∃ y : EuclideanSpace ℝ (Fin m), ‖y‖ = 1 ∧ ⟪y,h⟫ = ‖h‖ := by
    by_cases hz : h = 0
    · refine ⟨EuclideanSpace.single (⟨0,hm⟩ : Fin m) 1, by simp, ?_⟩
      simp [hz]
    · refine ⟨(‖h‖⁻¹ : ℝ) • h, norm_smul_inv_norm hz, ?_⟩
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
  obtain ⟨v,hv,hyv⟩ := hcov y hy1
  have hvh : (1-ε) * ‖h‖ ≤ ⟪v,h⟫ := by
    have heq : ⟪v,h⟫ = ⟪y,h⟫ - ⟪y-v,h⟫ := by rw [inner_sub_left]; ring
    have hb : ⟪y-v,h⟫ ≤ ε * ‖h‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hyv (norm_nonneg _))
    rw [heq,hyh]
    linarith
  refine le_ciInf fun u => ?_
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove ⟨v,hv⟩)
  have hu := inner_le_realSupportFunction hT (hU u.2) (-g)
  have heq : linForm (fun _ k => Fin.append (fun j => u.1 j) (fun i => v i) k) H
      = ⟪u.1,g⟫ + ⟪v,h⟫ := by
    simp [linForm, Fin.sum_univ_add, g, h, PiLp.inner_apply, mul_comm]
  rw [heq]
  rw [inner_neg_left, real_inner_comm] at hu
  change (1-ε) * ‖h‖ - realSupportFunction T (-g) ≤ _
  linarith

private theorem comparison_coeff_sum_sq {m n : ℕ}
    (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin m)) :
    (∑ _i : Fin 1, ∑ k : Fin (n+m),
      (Fin.append (fun j => u j) (fun i => v i) k -
       Fin.append (fun j => u' j) (fun i => v' i) k)^2)
      = ‖u-u'‖^2 + ‖v-v'‖^2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp [EuclideanSpace.real_norm_sq_eq]

private theorem restricted_minimum_scaled_bound {N n : ℕ} (hN : 0 < N)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : IsCompact T) (hne : T.Nonempty)
    (hunit : ∀ x ∈ T, ‖x‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    (1-ε) * (∫ x : EuclideanSpace ℝ (Fin N), ‖x‖ ∂stdGaussian _) - gaussianWidth T
      ≤ (∫ A, restrictedMinimum A T ∂gaussianMatrix (Fin N) (Fin n))
        + ε * ∫ A, specNorm A ∂gaussianMatrix (Fin N) (Fin n) := by
  -- finite `ε`-nets of the two unit spheres
  obtain ⟨Fu, hFuS, hFufin, hFucov⟩ := Metric.finite_approx_of_totallyBounded
    hT.totallyBounded ε hε
  obtain ⟨Fv, hFvS, hFvfin, hFvcov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).totallyBounded ε hε
  set U := hFufin.toFinset with hUdef
  set V := hFvfin.toFinset with hVdef
  have hU1 : ∀ u ∈ U, ‖u‖ = 1 := by
    intro u hu
    rw [hUdef, Set.Finite.mem_toFinset] at hu
    exact hunit _ (hFuS hu)
  have hV1 : ∀ v ∈ V, ‖v‖ = 1 := by
    intro v hv
    rw [hVdef, Set.Finite.mem_toFinset] at hv
    simpa using hFvS hv
  have hcovU : ∀ x ∈ T, ∃ u ∈ U, ‖x-u‖ ≤ ε := by
    intro x hx
    obtain ⟨y,hy,hyx⟩ := Set.mem_iUnion₂.1 (hFucov hx)
    refine ⟨y, by rw [hUdef, Set.Finite.mem_toFinset]; exact hy, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hyx
    exact hyx.le
  have hUsub : ↑U ⊆ T := by
    intro x hx
    rw [hUdef, Finset.mem_coe, Set.Finite.mem_toFinset] at hx
    exact hFuS hx
  have hcovV : ∀ x : EuclideanSpace ℝ (Fin N), ‖x‖ = 1 → ∃ v ∈ V, ‖x - v‖ ≤ ε := by
    intro x hx
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 := by simpa using hx
    obtain ⟨y, hy, hyx⟩ := Set.mem_iUnion₂.1 (hFvcov hx')
    refine ⟨y, by rw [hVdef, Set.Finite.mem_toFinset]; exact hy, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hyx; exact hyx.le
  have hUne : Nonempty U := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨u,hu,-⟩ := hcovU x hx
    exact ⟨⟨u,hu⟩⟩
  have hVne : Nonempty V := by
    obtain ⟨v, hv, -⟩ := hcovV (EuclideanSpace.single (⟨0, hN⟩ : Fin N) 1) (by simp)
    exact ⟨⟨v, hv⟩⟩
  -- the two Gaussian processes indexed by the nets
  set b : U → V → Fin 1 → Fin (n + N) → ℝ :=
    fun u v _ k => Fin.append (fun j => u.1 j) (fun i => v.1 i) k with hb
  set a : U → V → Fin N → Fin n → ℝ := fun u v i j => v.1 i * u.1 j with ha
  have hsame : ∀ (u : U) (t s : V),
      ∫ H, (linForm (b u t) H - linForm (b u s) H) ^ 2 ∂(gaussianMatrix (Fin 1) (Fin (n + N)))
        ≤ ∫ G, (linForm (a u t) G - linForm (a u s) G) ^ 2 ∂(gaussianMatrix (Fin N) (Fin n)) := by
    intro u t s
    simp_rw [linForm_sub_linForm]
    rw [integral_linForm_sq_gaussianMatrix, integral_linForm_sq_gaussianMatrix]
    simp only [ha, hb, Pi.sub_apply]
    rw [comparison_coeff_sum_sq]
    have hc := frobSq_vecMulVec_sub_same_eq_norm_sq u.1 t.1 s.1 (hU1 _ u.2)
    norm_num only [sub_self, norm_zero, zero_pow, zero_add]
    simpa only [frobSq_eq_sum_sq, Matrix.sub_apply, Matrix.vecMulVec_apply] using hc.ge
  have hdiff : ∀ (u v : U) (t s : V), u ≠ v →
      ∫ G, (linForm (a u t) G - linForm (a v s) G) ^ 2 ∂(gaussianMatrix (Fin N) (Fin n))
        ≤ ∫ H, (linForm (b u t) H - linForm (b v s) H) ^ 2 ∂(gaussianMatrix (Fin 1) (Fin (n + N))) := by
    intro u v t s _
    simp_rw [linForm_sub_linForm]
    rw [integral_linForm_sq_gaussianMatrix, integral_linForm_sq_gaussianMatrix]
    simp only [ha, hb, Pi.sub_apply]
    rw [comparison_coeff_sum_sq]
    simpa only [frobSq_eq_sum_sq, Matrix.sub_apply, Matrix.vecMulVec_apply] using
      frobSq_vecMulVec_sub_le_norm_sq_add u.1 v.1 t.1 s.1
        (hU1 _ u.2) (hU1 _ v.2) (hV1 _ t.2) (hV1 _ s.2)
  have hGM := gordon_minimax_inequality (fun u t H => linForm (b u t) H)
    (fun u t G => linForm (a u t) G)
    (hasGaussianLaw_linForm_gaussianMatrix (fun p : U × V => b p.1 p.2))
    (hasGaussianLaw_linForm_gaussianMatrix (fun p : U × V => a p.1 p.2))
    (fun u t => integral_linForm_gaussianMatrix _) (fun u t => integral_linForm_gaussianMatrix _)
    hsame hdiff
  -- integrability
  have hsMin : Integrable (fun A : Matrix (Fin N) (Fin n) ℝ => restrictedMinimum A T)
      (gaussianMatrix (Fin N) (Fin n)) :=
    (integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm _ 1 zero_le_one
      fun X Y => by
        rw [one_mul]
        exact abs_restrictedMinimum_sub_le_frobNorm X Y hT hne
          (fun x hx => (hunit x hx).le)).1
  have hspec : Integrable (fun A : Matrix (Fin N) (Fin n) ℝ => specNorm A)
      (gaussianMatrix (Fin N) (Fin n)) :=
    (integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm
      (fun A : Matrix (Fin N) (Fin n) ℝ => specNorm A) 1 zero_le_one
      fun X Y => by
        rw [one_mul]; exact abs_specNorm_sub_specNorm_le_frobNorm X Y).1
  have hXmm : Integrable (fun H => ⨅ u : U, ⨆ t : V, linForm (b u t) H)
      (gaussianMatrix (Fin 1) (Fin (n + N))) :=
    MeasureTheory.integrable_iInf_of_fintype (fun u H => ⨆ t : V, linForm (b u t) H)
      (fun u => MeasureTheory.integrable_iSup_of_fintype (fun t H => linForm (b u t) H)
        (fun t => integrable_linForm_gaussianMatrix _) (fun t => (continuous_linForm _).measurable))
      (fun u => Measurable.iSup fun t => (continuous_linForm _).measurable)
  have hYmm : Integrable (fun G => ⨅ u : U, ⨆ t : V, linForm (a u t) G)
      (gaussianMatrix (Fin N) (Fin n)) :=
    MeasureTheory.integrable_iInf_of_fintype (fun u G => ⨆ t : V, linForm (a u t) G)
      (fun u => MeasureTheory.integrable_iSup_of_fintype (fun t G => linForm (a u t) G)
        (fun t => integrable_linForm_gaussianMatrix _) (fun t => (continuous_linForm _).measurable))
      (fun u => Measurable.iSup fun t => (continuous_linForm _).measurable)
  let gn : Matrix (Fin 1) (Fin (n+N)) ℝ → EuclideanSpace ℝ (Fin n) :=
    fun H => WithLp.toLp 2 (fun j => H 0 (Fin.castAdd N j))
  let gm : Matrix (Fin 1) (Fin (n+N)) ℝ → EuclideanSpace ℝ (Fin N) :=
    fun H => WithLp.toLp 2 (fun i => H 0 (Fin.natAdd n i))
  have hrow := measurePreserving_gaussianMatrix_row (m := Fin 1) (n := Fin (n+N)) 0
  have hgmp := (measurePreserving_fst
    (μ := gaussianVector (Fin n)) (ν := gaussianVector (Fin N))).comp
    ((measurePreserving_gaussianVector_split n N).comp hrow)
  have hmmp := (measurePreserving_snd
    (μ := gaussianVector (Fin n)) (ν := gaussianVector (Fin N))).comp
    ((measurePreserving_gaussianVector_split n N).comp hrow)
  have hgLaw : HasLaw gn (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (gaussianMatrix (Fin 1) (Fin (n+N))) :=
    hasLaw_toLp_gaussianVector.comp ⟨hgmp.measurable.aemeasurable,hgmp.map_eq⟩
  have hmLaw : HasLaw gm (stdGaussian (EuclideanSpace ℝ (Fin N)))
      (gaussianMatrix (Fin 1) (Fin (n+N))) :=
    hasLaw_toLp_gaussianVector.comp ⟨hmmp.measurable.aemeasurable,hmmp.map_eq⟩
  let Uneg : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.neg ℝ
  have hnLaw : HasLaw Uneg (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨Uneg.continuous.measurable.aemeasurable,stdGaussian_map Uneg⟩
  have hngLaw : HasLaw (fun H => -gn H) (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (gaussianMatrix (Fin 1) (Fin (n+N))) := hnLaw.comp hgLaw
  have hsupp := integrable_realSupportFunction_stdGaussian hT hne
  have hg : Integrable (fun H => realSupportFunction T (-gn H))
      (gaussianMatrix (Fin 1) (Fin (n+N))) := by
    rw [← hngLaw.map_eq] at hsupp
    exact hsupp.comp_aemeasurable hngLaw.aemeasurable
  have hnorm : Integrable (fun x : EuclideanSpace ℝ (Fin N) => ‖x‖) (stdGaussian _) :=
    IsGaussian.integrable_id.norm
  have hh : Integrable (fun H => ‖gm H‖) (gaussianMatrix (Fin 1) (Fin (n+N))) := by
    rw [← hmLaw.map_eq] at hnorm
    exact hnorm.comp_aemeasurable hmLaw.aemeasurable
  calc
    (1-ε) * (∫ x : EuclideanSpace ℝ (Fin N), ‖x‖ ∂stdGaussian _) - gaussianWidth T
      = ∫ H, ((1-ε) * ‖gm H‖ - realSupportFunction T (-gn H))
          ∂gaussianMatrix (Fin 1) (Fin (n+N)) := by
        rw [integral_sub (hh.const_mul _) hg, integral_const_mul]
        have em : (∫ H, ‖gm H‖ ∂gaussianMatrix (Fin 1) (Fin (n+N)))
            = ∫ x : EuclideanSpace ℝ (Fin N), ‖x‖ ∂stdGaussian _ :=
          hmLaw.integral_comp hnorm.aestronglyMeasurable
        have eg : (∫ H, realSupportFunction T (-gn H) ∂gaussianMatrix (Fin 1) (Fin (n+N)))
            = gaussianWidth T := hngLaw.integral_comp
          (integrable_realSupportFunction_stdGaussian hT hne).aestronglyMeasurable
        rw [em,eg]
    _ ≤ ∫ H, (⨅ u : U, ⨆ t : V, linForm (b u t) H)
          ∂gaussianMatrix (Fin 1) (Fin (n+N)) := by
        refine integral_mono ((hh.const_mul _).sub hg) hXmm fun H => ?_
        exact gaussian_net_minimax_ge hN hT ε U V hUsub hcovV H
    _ ≤ ∫ G, (⨅ u : U, ⨆ t : V, linForm (a u t) G)
          ∂gaussianMatrix (Fin N) (Fin n) := hGM
    _ ≤ ∫ A, (restrictedMinimum A T + ε * specNorm A)
          ∂gaussianMatrix (Fin N) (Fin n) := by
        refine integral_mono hYmm (hsMin.add (hspec.const_mul ε)) fun G => ?_
        refine le_trans (le_of_eq ?_) (matrix_net_minimax_le G hT hne ε U V hV1 hcovU)
        congr 1; funext u; congr 1; funext t
        simp only [linForm, ha]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = (∫ A, restrictedMinimum A T ∂gaussianMatrix (Fin N) (Fin n))
          + ε * ∫ A, specNorm A ∂gaussianMatrix (Fin N) (Fin n) := by
        rw [integral_add hsMin (hspec.const_mul ε),integral_const_mul]


/-- The restricted minimum over a nonempty compact part of the unit sphere is
integrable for a standard Gaussian matrix. Source: the 1-Lipschitz property,
supplied reroute W5.
atlas: gaussian-width-restricted-minimum (partial) -/
theorem integrable_restrictedMinimum_gaussianMatrix {m n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : IsCompact T) (hne : T.Nonempty)
    (hunit : ∀ x ∈ T, ‖x‖ = 1) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => restrictedMinimum A T)
      (gaussianMatrix (Fin m) (Fin n)) :=
  (integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm _ 1 zero_le_one
    fun X Y => by
      rw [one_mul]
      exact abs_restrictedMinimum_sub_le_frobNorm X Y hT hne
        (fun x hx => (hunit x hx).le)).1

/-- Gordon comparison bounds the expected restricted minimum by the expected
row Gaussian norm minus the ordinary Gaussian width. The compact index set is
approximated by deterministic finite nets. Source: Tropp 2020, Theorem 6.8;
supplied reroutes W6–W8.
atlas: gaussian-width-restricted-minimum (partial) -/
theorem integral_norm_sub_gaussianWidth_le_integral_restrictedMinimum {m n : ℕ}
    (hm : 1 ≤ m) {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : IsCompact T) (hne : T.Nonempty) (hunit : ∀ x ∈ T, ‖x‖ = 1) :
    (∫ x : EuclideanSpace ℝ (Fin m), ‖x‖ ∂stdGaussian _) - gaussianWidth T
      ≤ ∫ A, restrictedMinimum A T ∂gaussianMatrix (Fin m) (Fin n) := by
  let EN := ∫ x : EuclideanSpace ℝ (Fin m), ‖x‖ ∂stdGaussian _
  let E := ∫ A, restrictedMinimum A T ∂gaussianMatrix (Fin m) (Fin n)
  let Sp := ∫ A, specNorm A ∂gaussianMatrix (Fin m) (Fin n)
  have hEN : 0 ≤ EN := integral_nonneg fun _ => norm_nonneg _
  have hSp : 0 ≤ Sp := integral_nonneg fun _ => specNorm_nonneg _
  have key : ∀ ε : ℝ, 0 < ε → EN - gaussianWidth T - ε*(EN+Sp) ≤ E := by
    intro ε hε
    have h := restricted_minimum_scaled_bound (by omega : 0 < m) hT hne hunit ε hε
    change (1-ε)*EN-gaussianWidth T ≤ E+ε*Sp at h
    linarith
  by_contra hcon
  push Not at hcon
  let δ := EN-gaussianWidth T-E
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let C := EN+Sp+1
  have hC : 0 < C := by dsimp [C]; linarith
  have h := key (δ/(2*C)) (by positivity)
  have hb : δ/(2*C)*(EN+Sp) ≤ δ/2 := by
    rw [div_mul_eq_mul_div,div_le_div_iff₀ (by positivity) (by norm_num)]
    dsimp [C]
    nlinarith
  dsimp [δ] at hb
  linarith

private theorem sqrt_sub_one_le_integral_norm_stdGaussian {m : ℕ} (hm : 1 ≤ m) :
    Real.sqrt m - 1 ≤ ∫ x : EuclideanSpace ℝ (Fin m), ‖x‖ ∂stdGaussian _ := by
  have h := sqrt_sub_sqrt_le_integral_sqrt_sum_sq_sub (N := m) (n := 1) le_rfl hm
  have hpos : 0 ≤ ∫ x : Fin 1 → ℝ, Real.sqrt (∑ i, x i^2) ∂gaussianVector (Fin 1) :=
    integral_nonneg fun _ => Real.sqrt_nonneg _
  have heq : (∫ x : Fin m → ℝ, Real.sqrt (∑ i, x i^2) ∂gaussianVector (Fin m))
      = ∫ x : EuclideanSpace ℝ (Fin m), ‖x‖ ∂stdGaussian _ := by
    have hh : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin m) => ‖x‖)
        (stdGaussian _) := continuous_norm.aestronglyMeasurable
    simpa only [Function.comp_apply, norm_eq_sqrt_sum_sq] using
      (hasLaw_toLp_gaussianVector (n := Fin m)).integral_comp hh
  rw [heq] at h
  norm_num only [Nat.cast_one, Real.sqrt_one] at h
  linarith

/-- The explicit expected restricted-minimum bound for a standard Gaussian
matrix, with standard-normal entries and no normalization by the row count.
Source: Tropp 2020, Theorem 6.8; supplied reroute W8.
atlas: gaussian-width-restricted-minimum (partial) -/
theorem sqrt_sub_one_sub_gaussianWidth_le_integral_restrictedMinimum {m n : ℕ}
    (hm : 1 ≤ m) {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : IsCompact T) (hne : T.Nonempty) (hunit : ∀ x ∈ T, ‖x‖ = 1) :
    Real.sqrt m - 1 - gaussianWidth T
      ≤ ∫ A, restrictedMinimum A T ∂gaussianMatrix (Fin m) (Fin n) :=
  (sub_le_sub_right (sqrt_sub_one_le_integral_norm_stdGaussian hm) _).trans
    (integral_norm_sub_gaussianWidth_le_integral_restrictedMinimum hm hT hne hunit)

/-- A standard Gaussian matrix escapes a compact subset of the unit sphere
with probability controlled by its ordinary Gaussian width. The strict event
also covers zero and negative thresholds without an atom hypothesis.
Source: Tropp 2020, Theorem 6.8, converted to standard-normal entries;
supplied reroute W9.
atlas: gaussian-width-restricted-minimum -/
theorem measureReal_restrictedMinimum_lt_sqrt_sub_gaussianWidth_le {m n : ℕ}
    (hm : 1 ≤ m) {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : IsCompact T) (hne : T.Nonempty) (hunit : ∀ x ∈ T, ‖x‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (gaussianMatrix (Fin m) (Fin n)).real
      {A | restrictedMinimum A T < Real.sqrt m-1-gaussianWidth T-t}
      ≤ Real.exp (-t^2/2) := by
  have hc := gaussian_concentration
    (fun A : Matrix (Fin m) (Fin n) ℝ => -restrictedMinimum A T) 1 zero_lt_one
    (fun X Y => by
      rw [neg_sub_neg, abs_sub_comm, one_mul]
      exact abs_restrictedMinimum_sub_le_frobNorm X Y hT hne (fun x hx => (hunit x hx).le)) t ht
  have hmean := sqrt_sub_one_sub_gaussianWidth_le_integral_restrictedMinimum hm hT hne hunit
  refine (measureReal_mono ?_).trans hc.2
  intro A hA
  change (∫ Y, -restrictedMinimum Y T ∂gaussianMatrix (Fin m) (Fin n)) + 1*t ≤ _
  rw [integral_neg,one_mul]
  change restrictedMinimum A T < _ at hA
  linarith

/-- The Gaussian-width restricted-minimum tail transported to any random
matrix having the standard Gaussian matrix law.
Source: Tropp 2020, Theorem 6.8; supplied reroute W9.
atlas: gaussian-width-restricted-minimum -/
theorem measureReal_restrictedMinimum_lt_sqrt_sub_gaussianWidth_le_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n : ℕ}
    {G : Ω → Matrix (Fin m) (Fin n) ℝ} (hG : HasLaw G (gaussianMatrix (Fin m) (Fin n)) μ)
    (hm : 1 ≤ m) {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : IsCompact T) (hne : T.Nonempty) (hunit : ∀ x ∈ T, ‖x‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | restrictedMinimum (G ω) T < Real.sqrt m-1-gaussianWidth T-t}
      ≤ Real.exp (-t^2/2) := by
  have hc : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => restrictedMinimum A T) :=
    continuous_of_abs_sub_le_mul_frobNorm _ 1 fun X Y => by
      rw [one_mul]
      exact abs_restrictedMinimum_sub_le_frobNorm X Y hT hne (fun x hx => (hunit x hx).le)
  rw [hG.measureReal_eq (measurableSet_lt hc.measurable measurable_const)]
  exact measureReal_restrictedMinimum_lt_sqrt_sub_gaussianWidth_le hm hT hne hunit t ht

end NLAlib
