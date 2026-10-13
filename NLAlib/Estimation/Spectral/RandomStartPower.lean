import NLAlib.Matrix.Spectral.PowerRayleigh
import NLAlib.RandomMatrix.Gaussian.Moments.LogOverlapMoments
import NLAlib.Matrix.Spectral.QuadraticProbe
import NLAlib.Krylov.Spectral.MeasurableRitz
import NLAlib.Krylov.Spectral.Ritz
/-!
# Expected error of Gaussian random-start power iteration

For a positive semidefinite `A` and a standard Gaussian start `b` (`gaussianVector ι`), the
relative error `(λ_max − ρ(A^q b))/λ_max` of the Rayleigh quotient after `q` matvecs has
expectation at most `min(1, (log(2n) + 2)/(2q + 1))` (gap-free, logarithmic in the dimension):
Kuczyński–Woźniakowski's random-start power method. The deterministic step is
`sub_rayleighQuotient_pow_div_specNorm_le_log_overlap_div` (a log-overlap bound), the
probabilistic step the logarithmic Gaussian overlap moments of
`NLAlib.RandomMatrix.Gaussian.Moments.LogOverlapMoments` transported to an arbitrary finite index
type.

Source: Kuczyński–Woźniakowski (1992) [`kw92`], Thm 4.1. Atlas: `random-start-power`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The relative error of the Rayleigh quotient of the `q`-th power iterate `A^q b` (`q`
matvecs) against the spectral norm: `(‖A‖₂ − ρ(A^q b))/‖A‖₂` (`= (λ_max − ρ)/λ_max` for
positive semidefinite `A`; junk value `0` at `A = 0`, where `‖A‖₂ = 0`).
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §2.
atlas: random-start-power -/
def powerRayleighRelativeError (A : Matrix ι ι ℝ) (b : ι → ℝ) (q : ℕ) : ℝ :=
  (specNorm A - rayleighQuotient A ((A ^ q) *ᵥ b)) / specNorm A

/-- The relative error of the zero matrix is `0`. Helper for `random-start-power`. -/
@[simp] theorem powerRayleighRelativeError_zero (b : ι → ℝ) (q : ℕ) :
    powerRayleighRelativeError (0 : Matrix ι ι ℝ) b q = 0 := by
  simp only [powerRayleighRelativeError, specNorm_zero, div_zero]

/-- The relative error is nonnegative for positive semidefinite `A` (the Rayleigh quotient is at
most the spectral norm). Helper for `random-start-power`. -/
theorem powerRayleighRelativeError_nonneg {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (b : ι → ℝ)
    (q : ℕ) : 0 ≤ powerRayleighRelativeError A b q := by
  have _ := hA
  exact div_nonneg (sub_nonneg.mpr (rayleighQuotient_le_specNorm A _)) (specNorm_nonneg A)

/-- The relative error is at most `1` for positive semidefinite `A` (the Rayleigh quotient is
nonnegative). Helper for `random-start-power`. -/
theorem powerRayleighRelativeError_le_one {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (b : ι → ℝ)
    (q : ℕ) : powerRayleighRelativeError A b q ≤ 1 := by
  by_cases hL : specNorm A = 0
  · simp only [powerRayleighRelativeError, hL, div_zero, zero_le_one]
  · have hLp : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne (Ne.symm hL)
    have h0 : 0 ≤ rayleighQuotient A ((A ^ q) *ᵥ b) := by
      rw [rayleighQuotient_eq_div]
      refine div_nonneg ?_ (dotProduct_self_nonneg _)
      simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg ((A ^ q) *ᵥ b)
    rw [powerRayleighRelativeError, div_le_one hLp]
    linarith

/-- The relative error is measurable in the start. Helper for `random-start-power`. -/
theorem measurable_powerRayleighRelativeError (A : Matrix ι ι ℝ) (q : ℕ) :
    Measurable (fun b : ι → ℝ => powerRayleighRelativeError A b q) := by
  unfold powerRayleighRelativeError
  simp only [rayleighQuotient_eq_div, Matrix.mulVec, dotProduct]
  fun_prop

/-! ### Gaussian facts on an arbitrary finite index type -/

section GaussianTransport

/-- Rotation invariance of the standard Gaussian vector in coordinates: for an orthonormal
basis `v` of `EuclideanSpace ℝ ι`, the coordinates `(⟪vᵢ, g⟫)ᵢ` of a standard Gaussian `g` are
i.i.d. standard Gaussian. Helper for `random-start-power` (Fintype form of
`measurePreserving_orthonormalBasis_repr_pi_gaussianReal`). -/
theorem measurePreserving_orthonormalBasis_repr_gaussianVector
    (v : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    MeasurePreserving (fun g : ι → ℝ => WithLp.ofLp (v.repr (WithLp.toLp 2 g)))
      (gaussianVector ι) (gaussianVector ι) := by
  have hm1 : Measurable (fun g : ι → ℝ => WithLp.toLp 2 g) := by fun_prop
  have hm2 : Measurable (fun x : EuclideanSpace ℝ ι => v.repr x) :=
    v.repr.continuous.measurable
  have hm3 : Measurable (fun y : EuclideanSpace ℝ ι => WithLp.ofLp y) := by fun_prop
  refine ⟨hm3.comp (hm2.comp hm1), ?_⟩
  have h := map_pi_eq_stdGaussian (ι := ι)
  have hfun : (fun g : ι → ℝ => WithLp.ofLp (v.repr (WithLp.toLp 2 g)))
      = (fun y : EuclideanSpace ℝ ι => WithLp.ofLp y) ∘ ((fun x => v.repr x) ∘
          (fun g : ι → ℝ => WithLp.toLp 2 g)) := rfl
  rw [hfun, ← Measure.map_map hm3 (hm2.comp hm1), ← Measure.map_map hm2 hm1, h]
  rw [show (fun x : EuclideanSpace ℝ ι => v.repr x) = ⇑v.repr from rfl, stdGaussian_map,
    ← h, Measure.map_map hm3 (by fun_prop)]
  exact Measure.map_id

/-- Coordinates in the eigenbasis of a real symmetric matrix preserve the standard Gaussian
vector law. Helper for `random-start-power`. -/
theorem measurePreserving_eigenvectorBasis_dotProduct_gaussianVector {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) :
    MeasurePreserving (fun b : ι → ℝ => fun i => (hA.eigenvectorBasis i : ι → ℝ) ⬝ᵥ b)
      (gaussianVector ι) (gaussianVector ι) := by
  have h := measurePreserving_orthonormalBasis_repr_gaussianVector hA.eigenvectorBasis
  have he : (fun b : ι → ℝ => WithLp.ofLp (hA.eigenvectorBasis.repr (WithLp.toLp 2 b))) =
      fun b : ι → ℝ => fun i => (hA.eigenvectorBasis i : ι → ℝ) ⬝ᵥ b := by
    funext b i
    rw [OrthonormalBasis.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    exact dotProduct_comm _ _
  rwa [he] at h

/-- Each eigenbasis coordinate of a standard Gaussian vector is nonzero almost surely.
Helper for `random-start-power`. -/
theorem ae_eigenvectorBasis_dotProduct_ne_zero_gaussianVector {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (i : ι) :
    ∀ᵐ b ∂(gaussianVector ι), (hA.eigenvectorBasis i : ι → ℝ) ⬝ᵥ b ≠ 0 := by
  let := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hMP := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).comp
    (measurePreserving_eigenvectorBasis_dotProduct_gaussianVector hA)
  have h := (gaussianReal 0 1).ae_ne 0
  rw [← hMP.map_eq] at h
  exact ae_of_ae_map hMP.measurable.aemeasurable h

/-- The logarithmic Gaussian overlap `log(‖c‖²/c_{i₀}²)` has first and second moments bounded by
`T + 2` and `T² + 4T + 8`, `T = log(2 |ι|)`, on an arbitrary finite index type (transport of
`integrable_and_integral_log_sum_div_sq_pi_gaussianReal_le` along `ι ≃ Fin (|ι|)`). -/
theorem log_overlap_moments_gaussianVector [Nonempty ι] (i₀ : ι) :
    Integrable (fun c : ι → ℝ => Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2)) (gaussianVector ι) ∧
    (∫ c, Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2) ∂(gaussianVector ι)) ≤
      Real.log (2 * (Fintype.card ι : ℝ)) + 2 ∧
    Integrable (fun c : ι → ℝ => Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2) ^ 2)
      (gaussianVector ι) ∧
    (∫ c, Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2) ^ 2 ∂(gaussianVector ι)) ≤
      Real.log (2 * (Fintype.card ι : ℝ)) ^ 2 + 4 * Real.log (2 * (Fintype.card ι : ℝ)) + 8 := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    ⟨Fintype.card ι - 1, by have := Fintype.card_pos (α := ι); omega⟩
  set e : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
  set F : (Fin (m + 1) → ℝ) → (ι → ℝ) :=
    fun x => MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm x
  have hF : MeasurePreserving F (gaussianVector (Fin (m + 1))) (gaussianVector ι) :=
    measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e.symm
  have hFapp : ∀ (x : Fin (m + 1) → ℝ) (i : ι), F x i = x (e i) := fun x i => by
    simp only [F]
    conv_lhs => rw [show i = e.symm (e i) from (e.symm_apply_apply i).symm]
    exact MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => ℝ) x (e i)
  have hcomp : ∀ x : Fin (m + 1) → ℝ,
      Real.log ((∑ i, F x i ^ 2) / (F x i₀) ^ 2) =
        Real.log ((∑ j, x j ^ 2) / (x (e i₀)) ^ 2) := fun x => by
    simp only [hFapp]
    rw [Equiv.sum_comp e (fun j => x j ^ 2)]
  obtain ⟨h1, h2, h3, h4⟩ :=
    integrable_and_integral_log_sum_div_sq_pi_gaussianReal_le m (e i₀)
  have hcard : ((m + 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) := by rw [hm]
  have hL1 : Integrable (fun c : ι → ℝ => Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2))
      (gaussianVector ι) := by
    rw [← hF.map_eq]
    refine (integrable_map_measure ?_ hF.measurable.aemeasurable).2 ?_
    · exact (Measurable.log (by fun_prop)).aestronglyMeasurable
    · exact h1.congr (ae_of_all _ fun x => (hcomp x).symm)
  have hL2 : Integrable (fun c : ι → ℝ => Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2) ^ 2)
      (gaussianVector ι) := by
    rw [← hF.map_eq]
    refine (integrable_map_measure ?_ hF.measurable.aemeasurable).2 ?_
    · exact ((Measurable.log (by fun_prop)).pow_const 2).aestronglyMeasurable
    · exact h3.congr (ae_of_all _ fun x => by rw [Function.comp_apply, hcomp x])
  refine ⟨hL1, ?_, hL2, ?_⟩
  · rw [← hF.map_eq, integral_map hF.measurable.aemeasurable
      (Measurable.log (by fun_prop)).aestronglyMeasurable]
    simp_rw [hcomp]
    rw [← hcard]; exact h2
  · rw [← hF.map_eq, integral_map hF.measurable.aemeasurable
      ((Measurable.log (by fun_prop)).pow_const 2).aestronglyMeasurable]
    simp_rw [hcomp]
    rw [← hcard]; exact h4

end GaussianTransport

/-- For a positive semidefinite `A`, the spectral norm is the largest eigenvalue
`hA.isHermitian.eigenvalues₀ 0`. Helper for `random-start-power`. -/
theorem _root_.Matrix.PosSemidef.specNorm_eq_eigenvalues₀_zero [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : specNorm A = hA.isHermitian.eigenvalues₀ 0 := by
  rw [specNorm_eq_norm_eigenvalues hA.isHermitian]
  have hnn : ∀ i, 0 ≤ hA.isHermitian.eigenvalues i := hA.eigenvalues_nonneg
  have htop : ∀ i, hA.isHermitian.eigenvalues i ≤ hA.isHermitian.eigenvalues₀ 0 :=
    hA.isHermitian.eigenvalues_le_eigenvalues₀_zero
  have h0 : 0 ≤ hA.isHermitian.eigenvalues₀ 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›; exact (hnn i).trans (htop i)
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg h0]
    intro i
    rw [Real.norm_of_nonneg (hnn i)]
    exact htop i
  · have := norm_le_pi_norm hA.isHermitian.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) 0)
    rwa [hA.isHermitian.eigenvalues_equivOfCardEq, Real.norm_of_nonneg h0] at this

/-- **Random-start power iteration, expected relative error.** For a positive semidefinite
`A : Matrix ι ι ℝ` and a standard Gaussian start `b`, after `q` matvecs
`𝔼[(λ_max − ρ(A^q b))/λ_max] ≤ min(1, (log(2|ι|) + 2)/(2q + 1))`. Valid for every `q`
(including `q = 0`), every dimension and the zero matrix; no eigenvalue gap or overlap moment is
assumed. Source: Kuczyński–Woźniakowski (1992) [`kw92`], Thm 4.1 (the gap-free bound).
atlas: random-start-power -/
theorem integral_powerRayleighRelativeError_gaussianVector_le {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (q : ℕ) :
    (∫ b, powerRayleighRelativeError A b q ∂(gaussianVector ι)) ≤
      min 1 ((Real.log (2 * (Fintype.card ι : ℝ)) + 2) / ((2 * q + 1 : ℕ) : ℝ)) := by
  let μ := gaussianVector ι
  let T := Real.log (2 * (Fintype.card ι : ℝ))
  let r := ((2 * q + 1 : ℕ) : ℝ)
  have hr : 0 < r := by dsimp only [r]; exact_mod_cast (by omega : 0 < 2 * q + 1)
  have hfm := measurable_powerRayleighRelativeError A q
  have hfi : Integrable (fun b => powerRayleighRelativeError A b q) μ := by
    refine (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable ?_
    exact ae_of_all _ fun b => by
      rw [Real.norm_of_nonneg (powerRayleighRelativeError_nonneg hA b q)]
      exact powerRayleighRelativeError_le_one hA b q
  have hOne : (∫ b, powerRayleighRelativeError A b q ∂μ) ≤ 1 := by
    have h := integral_mono hfi (integrable_const (1 : ℝ))
      (fun b => powerRayleighRelativeError_le_one hA b q)
    simpa only [integral_const, probReal_univ, one_smul] using h
  apply le_min hOne
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hzero : A = 0 := Subsingleton.elim _ _
    rw [hzero]
    simp only [powerRayleighRelativeError_zero, integral_zero]
    have : (0 : ℝ) ≤ T + 2 := by
      simp only [T, Fintype.card_eq_zero, Nat.cast_zero, mul_zero, Real.log_zero]; norm_num
    exact div_nonneg this hr.le
  have hT : 0 ≤ T := by
    apply Real.log_nonneg
    have hn : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  by_cases hZero : specNorm A = 0
  · simp only [powerRayleighRelativeError, hZero, div_zero, integral_zero]
    exact div_nonneg (by linarith) hr.le
  · have hL : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne (Ne.symm hZero)
    set i₀ : ι := Fintype.equivOfCardEq (Fintype.card_fin _) (0 : Fin (Fintype.card ι))
    have h₀ : hA.isHermitian.eigenvalues i₀ = specNorm A := by
      rw [hA.specNorm_eq_eigenvalues₀_zero, hA.isHermitian.eigenvalues_equivOfCardEq]
    let C := fun b : ι → ℝ => fun i => (hA.isHermitian.eigenvectorBasis i : ι → ℝ) ⬝ᵥ b
    have hMP : MeasurePreserving C μ μ :=
      measurePreserving_eigenvectorBasis_dotProduct_gaussianVector hA.isHermitian
    let L := fun c : ι → ℝ => Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2)
    have hLm : Measurable L := by dsimp only [L]; fun_prop
    obtain ⟨hLI, hLV, _, _⟩ := log_overlap_moments_gaussianVector (ι := ι) i₀
    have hLCI : Integrable (fun b => L (C b)) μ := by
      apply (integrable_map_measure hLm.aestronglyMeasurable hMP.measurable.aemeasurable).mp
      rwa [hMP.map_eq]
    have hLCV : (∫ b, L (C b) ∂μ) ≤ T + 2 := by
      have h := integral_map (μ := μ) hMP.measurable.aemeasurable hLm.aestronglyMeasurable
      rw [hMP.map_eq] at h
      exact h.symm.trans_le hLV
    have hNZ : ∀ᵐ b ∂μ, C b i₀ ≠ 0 :=
      ae_eigenvectorBasis_dotProduct_ne_zero_gaussianVector hA.isHermitian i₀
    have hPoint : (fun b => powerRayleighRelativeError A b q) ≤ᵐ[μ] fun b => L (C b) / r := by
      filter_upwards [hNZ] with b hb
      have h := sub_rayleighQuotient_pow_div_specNorm_le_log_overlap_div hA hL i₀ h₀ b hb q
      rw [← sum_sq_eigenvectorBasis_dotProduct hA.isHermitian b] at h
      simpa only [powerRayleighRelativeError, rayleighQuotient_toEuclideanCLM_eq] using h
    have h := integral_mono_ae hfi (hLCI.div_const r) hPoint
    rw [integral_div] at h
    exact h.trans (div_le_div_of_nonneg_right hLCV hr.le)

/-- `integral_powerRayleighRelativeError_gaussianVector_le` for a random start with the
standard Gaussian law on an abstract probability space. Source: Kuczyński–Woźniakowski (1992)
[`kw92`], Thm 4.1.
atlas: random-start-power -/
theorem integral_powerRayleighRelativeError_le_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (q : ℕ) {G : Ω → ι → ℝ}
    (hG : HasLaw G (gaussianVector ι) μ) :
    (∫ ω, powerRayleighRelativeError A (G ω) q ∂μ) ≤
      min 1 ((Real.log (2 * (Fintype.card ι : ℝ)) + 2) / ((2 * q + 1 : ℕ) : ℝ)) := by
  have h : (∫ ω, powerRayleighRelativeError A (G ω) q ∂μ) = _ :=
    hG.integral_comp (measurable_powerRayleighRelativeError A q).aestronglyMeasurable
  exact h.trans_le (integral_powerRayleighRelativeError_gaussianVector_le hA q)

/-- **Random-start power iteration, coarse rate**: for `q ≥ 1` and `|ι| ≥ 2`,
`𝔼[(λ_max − ρ(A^q b))/λ_max] ≤ 3 log|ι| / q`. Source: Kuczyński–Woźniakowski (1992) [`kw92`],
Thm 4.1 (coarse form).
atlas: random-start-power -/
theorem integral_powerRayleighRelativeError_le_three_log_div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {q : ℕ} (hq : 1 ≤ q) (hn : 2 ≤ Fintype.card ι)
    {G : Ω → ι → ℝ} (hG : HasLaw G (gaussianVector ι) μ) :
    (∫ ω, powerRayleighRelativeError A (G ω) q ∂μ) ≤
      3 * Real.log (Fintype.card ι : ℝ) / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hn2 : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < Fintype.card ι := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogn : Real.log 2 ≤ Real.log (Fintype.card ι : ℝ) := Real.log_le_log (by norm_num) hn2
  have hT : Real.log (2 * (Fintype.card ι : ℝ)) + 2 ≤ 6 * Real.log (Fintype.card ι : ℝ) := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    linarith
  have hr : (0 : ℝ) < ((2 * q + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q + 1)
  have hc : (Real.log (2 * (Fintype.card ι : ℝ)) + 2) / ((2 * q + 1 : ℕ) : ℝ) ≤
      3 * Real.log (Fintype.card ι : ℝ) / q := by
    apply (div_le_div_iff₀ hr hq0).mpr
    have h := mul_le_mul_of_nonneg_right hT hq0.le
    push_cast
    nlinarith
  exact ((integral_powerRayleighRelativeError_le_of_hasLaw hA q hG).trans
    (min_le_right _ _)).trans hc

end NLAlib
