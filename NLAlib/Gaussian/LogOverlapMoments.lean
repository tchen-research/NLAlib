import NLAlib.Gaussian.LogOverlap
import NLAlib.ForMathlib.Probability.ExponentialTailMoments
import NLAlib.Matrix.PolynomialCalculus

/-!
# First and second moments of Gaussian logarithmic overlap

The nonnegative excess above `log(2N)` has half-rate exponential tail. Integrating
that excess gives the manuscript's exact first and second logarithmic moment bounds.
Source: manuscript `rt:log-moments`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- Gaussian logarithmic overlap has both finite moments with the source's exact
constants. Source: manuscript `rt:log-moments`; the dimension is `N = n+1`.
The null head-zero set uses totalized division, and no inverse-head-square
expectation is used or assumed.
atlas: random-start-power (partial) -/
theorem integrable_and_integral_gaussianLogOverlap_le (n : ℕ) :
    let μ := Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1
    let T := Real.log (2 * ((n + 1 : ℕ) : ℝ))
    Integrable (@gaussianLogOverlap n) μ ∧
      (∫ g, gaussianLogOverlap g ∂μ) ≤ T + 2 ∧
      Integrable (fun g => gaussianLogOverlap g ^ 2) μ ∧
      (∫ g, gaussianLogOverlap g ^ 2 ∂μ) ≤ T ^ 2 + 4 * T + 8 := by
  dsimp only
  let μ := Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1
  let T := Real.log (2 * ((n + 1 : ℕ) : ℝ))
  let Z := fun g : Fin (n + 1) → ℝ => max (gaussianLogOverlap g - T) 0
  have hT : 0 ≤ T := by
    apply Real.log_nonneg
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    linarith
  have hZm : Measurable Z := (measurable_gaussianLogOverlap n |>.sub measurable_const).max measurable_const
  have hZ0 : ∀ g, 0 ≤ Z g := fun _ => le_max_right _ _
  have hZtail : ∀ t : ℝ, 0 < t → μ {g | t < Z g} ≤ ENNReal.ofReal (Real.exp (-t / 2)) := by
    intro t ht
    have he : {g : Fin (n + 1) → ℝ | t < Z g} = {g | T + t < gaussianLogOverlap g} := by
      ext g
      change (t < max (gaussianLogOverlap g - T) 0) ↔ (T + t < gaussianLogOverlap g)
      rw [lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        left
        linarith
    have hC : Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) = Real.exp (T / 2) := by
      rw [Real.exp_half]
      change _ = Real.sqrt (Real.exp (Real.log (2 * ((n + 1 : ℕ) : ℝ))))
      rw [Real.exp_log (by positivity)]
    have hExp : Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) * Real.exp (-(T + t) / 2) =
        Real.exp (-t / 2) := by
      rw [hC, ← Real.exp_add]
      congr 1
      ring
    have h := pi_gaussianReal_logOverlap_gt_le n (t := T + t) (by dsimp only [T]; linarith)
    rw [he]
    simpa only [hExp] using h
  obtain ⟨hZI, hZv, hZI2, hZv2⟩ :=
    integrable_and_integral_sq_le_of_exp_neg_half_tail Z hZm hZ0 hZtail
  have hLm := measurable_gaussianLogOverlap n
  have hL0 := @gaussianLogOverlap_nonneg n
  have hLbound : ∀ g : Fin (n + 1) → ℝ, gaussianLogOverlap g ≤ T + Z g := by
    intro g
    have h := le_max_left (gaussianLogOverlap g - T) 0
    linarith
  have hLI : Integrable (@gaussianLogOverlap n) μ := by
    refine ((integrable_const T).add hZI).mono' hLm.aestronglyMeasurable ?_
    exact ae_of_all _ fun g => by
      rw [Real.norm_of_nonneg (hL0 g)]
      exact hLbound g
  have hLsqbound : ∀ g : Fin (n + 1) → ℝ, gaussianLogOverlap g ^ 2 ≤
      T ^ 2 + (2 * T) * Z g + Z g ^ 2 := by
    intro g
    have h := pow_le_pow_left₀ (hL0 g) (hLbound g) 2
    nlinarith
  have hRightI : Integrable (fun g => T ^ 2 + (2 * T) * Z g + Z g ^ 2) μ :=
    ((integrable_const (T ^ 2)).add (hZI.const_mul (2 * T))).add hZI2
  have hLI2 : Integrable (fun g => gaussianLogOverlap g ^ 2) μ := by
    refine hRightI.mono' (hLm.pow_const 2).aestronglyMeasurable ?_
    exact ae_of_all _ fun g => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hLsqbound g
  refine ⟨hLI, ?_, hLI2, ?_⟩
  · have h := integral_mono hLI ((integrable_const T).add hZI) hLbound
    simp only [Pi.add_apply] at h
    rw [integral_add (integrable_const T) hZI, integral_const, probReal_univ, one_smul] at h
    linarith
  · have h := integral_mono hLI2 hRightI hLsqbound
    have hSumI : Integrable (fun g => T ^ 2 + (2 * T) * Z g) μ :=
      (integrable_const (T ^ 2)).add (hZI.const_mul (2 * T))
    rw [integral_add hSumI hZI2,
      integral_add (integrable_const (T ^ 2)) (hZI.const_mul (2 * T)),
      integral_const, probReal_univ, one_smul, integral_const_mul] at h
    nlinarith

/-- Any one fixed Gaussian coordinate has the same logarithmic inverse-overlap
moment bounds. Source: manuscript `rt:log-moments`; coordinate permutation invariance
lets a deterministic top eigenvector use its own eigenbasis label. -/
theorem integrable_and_integral_log_sum_div_sq_pi_gaussianReal_le (n : ℕ) (i : Fin (n + 1)) :
    let μ := Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1
    let T := Real.log (2 * ((n + 1 : ℕ) : ℝ))
    let L := fun g : Fin (n + 1) → ℝ => Real.log ((∑ j, g j ^ 2) / (g i) ^ 2)
    Integrable L μ ∧ (∫ g, L g ∂μ) ≤ T + 2 ∧
      Integrable (fun g => L g ^ 2) μ ∧ (∫ g, L g ^ 2 ∂μ) ≤ T ^ 2 + 4 * T + 8 := by
  dsimp only
  let μ := Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1
  let L := fun g : Fin (n + 1) → ℝ => Real.log ((∑ j, g j ^ 2) / (g i) ^ 2)
  let e := Equiv.swap (0 : Fin (n + 1)) i
  let F := MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) => ℝ) e
  have hMP : MeasurePreserving F μ μ :=
    measurePreserving_piCongrLeft (fun _ : Fin (n + 1) => gaussianReal 0 1) e
  have hF : ∀ g j, F g j = g (e.symm j) := by
    intro g j
    simpa only [Equiv.apply_symm_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (n + 1) => ℝ) e g (e.symm j)
  have hEq : ∀ g, gaussianLogOverlap (F g) = L g := by
    intro g
    rw [gaussianLogOverlap_eq_log_sum_div_sq]
    have hS : (∑ j, F g j ^ 2) = ∑ j, g j ^ 2 := by
      simp only [hF]
      exact e.symm.sum_comp (fun j => g j ^ 2)
    have h0 : F g 0 = g i := by rw [hF]; simp [e]
    rw [hS, h0]
  obtain ⟨hI, hV, hI2, hV2⟩ := integrable_and_integral_gaussianLogOverlap_le n
  have hLI : Integrable L μ := by
    have h := (hMP.integrable_comp_emb F.measurableEmbedding (g := @gaussianLogOverlap n)).mpr hI
    exact h.congr (ae_of_all _ hEq)
  have hLI2 : Integrable (fun g => L g ^ 2) μ := by
    have h := (hMP.integrable_comp_emb F.measurableEmbedding
      (g := fun g => gaussianLogOverlap g ^ 2)).mpr hI2
    exact h.congr (ae_of_all _ fun g => congrArg (fun x : ℝ => x ^ 2) (hEq g))
  have hLV : (∫ g, L g ∂μ) = ∫ g, gaussianLogOverlap g ∂μ := by
    calc (∫ g, L g ∂μ) = ∫ g, gaussianLogOverlap (F g) ∂μ :=
        integral_congr_ae (ae_of_all _ fun g => (hEq g).symm)
      _ = _ := hMP.integral_comp' (@gaussianLogOverlap n)
  have hLV2 : (∫ g, L g ^ 2 ∂μ) = ∫ g, gaussianLogOverlap g ^ 2 ∂μ := by
    calc (∫ g, L g ^ 2 ∂μ) = ∫ g, gaussianLogOverlap (F g) ^ 2 ∂μ :=
        integral_congr_ae (ae_of_all _ fun g => congrArg (fun x : ℝ => x ^ 2) (hEq g).symm)
      _ = _ := hMP.integral_comp' (fun g => gaussianLogOverlap g ^ 2)
  exact ⟨hLI, hLV.trans_le hV, hLI2, hLV2.trans_le hV2⟩

/-- Coordinates in the fixed eigenbasis of a real symmetric matrix preserve the
standard Gaussian vector law. Source: Gaussian rotation invariance; manuscript
`rt:random-start`, fixed eigenbasis coordinates. -/
theorem measurePreserving_eigenvectorBasis_dotProduct_pi_gaussianReal {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    MeasurePreserving (fun b : Fin n → ℝ =>
      fun i => (hA.eigenvectorBasis i : Fin n → ℝ) ⬝ᵥ b)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have h := measurePreserving_orthonormalBasis_repr_pi_gaussianReal hA.eigenvectorBasis
  have he : (fun b : Fin n → ℝ => WithLp.ofLp (hA.eigenvectorBasis.repr (WithLp.toLp 2 b))) =
      fun b : Fin n → ℝ => fun i => (hA.eigenvectorBasis i : Fin n → ℝ) ⬝ᵥ b := by
    funext b i
    rw [OrthonormalBasis.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    exact dotProduct_comm _ _
  rwa [he] at h

/-- Each fixed top-eigenvector Gaussian overlap is nonzero almost surely.
Source: Gaussian rotation invariance and atomlessness; manuscript `rt:random-start`. -/
theorem ae_eigenvectorBasis_dotProduct_ne_zero_pi_gaussianReal {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (i : Fin n) :
    ∀ᵐ b ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1),
      (hA.eigenvectorBasis i : Fin n → ℝ) ⬝ᵥ b ≠ 0 := by
  let := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hMP := (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).comp
    (measurePreserving_eigenvectorBasis_dotProduct_pi_gaussianReal hA)
  have h := (gaussianReal 0 1).ae_ne 0
  rw [← hMP.map_eq] at h
  exact ae_of_ae_map hMP.measurable.aemeasurable h

end NLAlib
