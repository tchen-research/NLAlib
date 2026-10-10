import NLAlib.Gaussian.InverseMoments.WeakInequality
import NLAlib.Gaussian.InverseMoments.RegularizedApproximation
import NLAlib.Gaussian.InverseMoments.ResolventLimit
import NLAlib.Gaussian.InverseMoments.HardEdgeEndpoint
import NLAlib.Gaussian.PolynomialGrowth
import NLAlib.Matrix.CoordinateUpdates
import NLAlib.Matrix.GramSoftMinMeasurable
import NLAlib.Gaussian.InverseMoments.RegularizedIntegrability

/-!
# The Gaussian hard-edge weak inequality by operator regularization

Actual regularized Gram derivatives satisfy coordinate Stein identities.
Their inverse-power limits and a one-sided Fatou argument give the sharp
scalar weak inequality for the smallest squared singular value.

Source: operator hard-edge derivation; atlas `wishart-lambda-min-tail`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.L2Operator

namespace NLAlib

private lemma matrix_entry_sq_le_frobSq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : Matrix ι κ ℝ) (i : ι) (j : κ) : G i j ^ 2 ≤ frobSq G := by
  unfold frobSq frobInner
  simp only [← sq]
  exact (Finset.single_le_sum (fun a _ => sq_nonneg (G i a)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg (G a b))
      (Finset.mem_univ i))

private lemma norm_weak_expression_le {ψ ψ' : ℝ → ℝ} {P Q s A B b y : ℝ}
    (_hP : 0 ≤ P) (hQ : 0 ≤ Q) (hs : 0 ≤ s) (hA : 0 ≤ A) (hAs : A ≤ 4 * s)
    (hBs : |B| ≤ 2 * s) (hψ : ‖ψ y‖ ≤ P) (hψ' : ‖ψ' y‖ ≤ Q) :
    ‖ψ' y * A + (b - B) * ψ y‖ ≤ (4 * Q + 2 * P) * s + |b| * P := by
  have hfirst : ‖ψ' y * A‖ ≤ Q * (4 * s) := by
    rw [norm_mul, Real.norm_of_nonneg hA]
    exact mul_le_mul hψ' hAs hA hQ
  have hsecond : ‖(b - B) * ψ y‖ ≤ (|b| + 2 * s) * P := by
    rw [norm_mul, Real.norm_eq_abs]
    have hsub : |b - B| ≤ |b| + 2 * s := (abs_sub b B).trans (add_le_add le_rfl hBs)
    exact mul_le_mul hsub hψ (norm_nonneg _) (by positivity)
  calc _ ≤ ‖ψ' y * A‖ + ‖(b - B) * ψ y‖ := norm_add_le _ _
    _ ≤ Q * (4 * s) + (|b| + 2 * s) * P := add_le_add hfirst hsecond
    _ = _ := by ring

private lemma hasDerivAt_softMin_update
    {r k : ℕ} (hr : 1 ≤ r) (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (x : Fin r × Fin k → ℝ) (i : Fin r × Fin k) (t : ℝ) :
    HasDerivAt (fun y : ℝ => inversePowerSoftMin n
      (regularizedGram ε (Matrix.of (fun a b => Function.update x i y (a, b)))))
      (gramSoftMinGradient n ε (Matrix.of (fun a b => Function.update x i t (a, b))) i.1 i.2) t := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let H : Matrix (Fin r) (Fin k) ℝ := Matrix.of (fun a b => Function.update x i t (a, b))
  let E : Matrix (Fin r) (Fin k) ℝ := Matrix.single i.1 i.2 1
  have heq (y : ℝ) : Matrix.of (fun a b => Function.update x i y (a, b)) = H + (y - t) • E := by
    have h := matrixOf_curry_update_eq_add_single (Function.update x i t) i.1 i.2 y
    simpa only [Prod.mk.eta, Function.update_idem, Function.update_self] using h
  have h := (hasDerivAt_gramSoftMin_single_zero n hn hε H i.1 i.2).comp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  simpa only [Function.comp_def, heq, sub_self, mul_one, id_eq, zero_smul, add_zero, E] using h

private lemma hasDerivAt_gradient_update
    {r k : ℕ} (hr : 1 ≤ r) (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (x : Fin r × Fin k → ℝ) (i : Fin r × Fin k) (t : ℝ) :
    HasDerivAt (fun y : ℝ =>
      gramSoftMinGradient n ε (Matrix.of (fun a b => Function.update x i y (a, b))) i.1 i.2)
      (gramSoftMinSecond n ε (Matrix.of (fun a b => Function.update x i t (a, b)))
        (Matrix.single i.1 i.2 1)) t := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let H : Matrix (Fin r) (Fin k) ℝ := Matrix.of (fun a b => Function.update x i t (a, b))
  let E : Matrix (Fin r) (Fin k) ℝ := Matrix.single i.1 i.2 1
  have heq (y : ℝ) : Matrix.of (fun a b => Function.update x i y (a, b)) = H + (y - t) • E := by
    have h := matrixOf_curry_update_eq_add_single (Function.update x i t) i.1 i.2 y
    simpa only [Prod.mk.eta, Function.update_idem, Function.update_self] using h
  have h := (hasDerivAt_gramSoftMinGradient_single_zero n hn hε H i.1 i.2).comp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  simpa only [Function.comp_def, heq, sub_self, mul_one, id_eq, zero_smul, add_zero, E] using h

private lemma integrable_mul_bounded_test {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f φ : Ω → ℝ) (hf : Integrable f μ) (hφ : Measurable φ)
    (P : ℝ) (hP : ∀ x, ‖φ x‖ ≤ P) : Integrable (fun x => φ x * f x) μ := by
  refine (hf.norm.const_mul P).mono' (hφ.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  exact ae_of_all _ fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hP x) (norm_nonneg _)

private theorem integral_weak_shift_nonneg_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (ε : ℝ) (hε : 0 < ε)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hψP : ∀ x, ‖ψ x‖ ≤ P) (hψQ : ∀ x, ‖deriv ψ x‖ ≤ Q) :
    0 ≤ ∫ G : Fin r → Fin k → ℝ,
      deriv ψ (sigmaMin (Matrix.of G)ᵀ ^ 2 + ε) * (4 * sigmaMin (Matrix.of G)ᵀ ^ 2) +
        (2 * ((k : ℝ) - r + 1) - 2 * sigmaMin (Matrix.of G)ᵀ ^ 2) *
          ψ (sigmaMin (Matrix.of G)ᵀ ^ 2 + ε) ∂(gaussianMatrix r k) := by
  classical
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let μ := gaussianMatrix r k
  let ν : Measure ((Fin r × Fin k) → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let e := MeasurableEquiv.curry (Fin r) (Fin k) ℝ
  have hmp : MeasurePreserving e ν μ := ⟨e.measurable, (gaussianMatrix_eq_map_curry r k).symm⟩
  let G : ((Fin r × Fin k) → ℝ) → Matrix (Fin r) (Fin k) ℝ := fun x => Matrix.of (e x)
  let X : ((Fin r × Fin k) → ℝ) → ℝ := fun x => sigmaMin (G x)ᵀ ^ 2
  let S : ((Fin r × Fin k) → ℝ) → ℝ := fun x => frobSq (G x)
  let F : ℕ → ((Fin r × Fin k) → ℝ) → ℝ :=
    fun n x => inversePowerSoftMin (n + 1) (regularizedGram ε (G x))
  let D : ℕ → (Fin r × Fin k) → ((Fin r × Fin k) → ℝ) → ℝ :=
    fun n i x => gramSoftMinGradient (n + 1) ε (G x) i.1 i.2
  let DD : ℕ → (Fin r × Fin k) → ((Fin r × Fin k) → ℝ) → ℝ :=
    fun n i x => gramSoftMinSecond (n + 1) ε (G x) (Matrix.single i.1 i.2 1)
  let b : ℝ := 2 * ((k : ℝ) - r + 1)
  have hSi : Integrable S ν := hmp.integrable_comp_of_integrable (integrable_frobSq_gaussianMatrix r k)
  have hSnn (x) : 0 ≤ S x := frobSq_nonneg _
  have hFm (n) : Measurable (F n) :=
    (measurable_inversePowerSoftMin_regularizedGram (n + 1) ε).comp e.measurable
  have hDm (n i) : Measurable (D n i) :=
    (measurable_gramSoftMinGradient_entry (n + 1) ε i.1 i.2).comp e.measurable
  have hDDm (n i) : Measurable (DD n i) :=
    (measurable_gramSoftMinSecond_single (n + 1) ε i.1 i.2).comp e.measurable
  have henergy (n x) : (∑ i, D n i x ^ 2) = frobSq (gramSoftMinGradient (n + 1) ε (G x)) := by
    simp only [Fintype.sum_prod_type, D, frobSq, frobInner, ← sq]
  have heuler (n x) : (∑ i, x i * D n i x) = frobInner (G x) (gramSoftMinGradient (n + 1) ε (G x)) := by
    simp only [Fintype.sum_prod_type, D, frobInner, G, e, MeasurableEquiv.curry_apply, Matrix.of_apply]
  have hlap (n x) : (∑ i, DD n i x) = gramSoftMinLaplacian (n + 1) ε (G x) := by
    simp only [Fintype.sum_prod_type, DD, gramSoftMinLaplacian]
  have hAs (n x) : (∑ i, D n i x ^ 2) ≤ 4 * S x := by
    rw [henergy]
    exact frobSq_gramSoftMinGradient_le (n + 1) (by omega) hε (G x)
  have hBs (n x) : |∑ i, x i * D n i x| ≤ 2 * S x := by
    rw [heuler]
    exact abs_frobInner_gramSoftMinGradient_le (n + 1) (by omega) hε (G x)
  have hDiSq (n i x) : D n i x ^ 2 ≤ 4 * S x :=
    (matrix_entry_sq_le_frobSq _ i.1 i.2).trans
      (frobSq_gramSoftMinGradient_le (n + 1) (by omega) hε (G x))
  have hDi (n i) : Integrable (D n i) ν := by
    refine ((integrable_const (1 : ℝ)).add (hSi.const_mul 4)).mono' (hDm n i).aestronglyMeasurable ?_
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      change |D n i x| ≤ 1 + 4 * S x
      have h := hDiSq n i x
      nlinarith [sq_nonneg (|D n i x| - 1), sq_abs (D n i x)]
  have hDi2 (n i) : Integrable (fun x => D n i x ^ 2) ν := by
    refine (hSi.const_mul 4).mono' ((hDm n i).pow_const 2).aestronglyMeasurable ?_
    exact ae_of_all _ fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hDiSq n i x
  have hxiDi (n i) : Integrable (fun x => x i * D n i x) ν := by
    refine (hSi.const_mul 5).mono' ((measurable_pi_apply i).mul (hDm n i)).aestronglyMeasurable ?_
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      have hx : (x i) ^ 2 ≤ S x := matrix_entry_sq_le_frobSq (G x) i.1 i.2
      have hd := hDiSq n i x
      nlinarith [sq_nonneg (|x i| - |D n i x|), sq_abs (x i), sq_abs (D n i x)]
  have hψm (n) : Measurable (fun x => ψ (F n x)) := hψ.continuous.measurable.comp (hFm n)
  have hψ'm (n) : Measurable (fun x => deriv ψ (F n x)) :=
    (hψ.continuous_deriv le_rfl).measurable.comp (hFm n)
  have hψi (n) : Integrable (fun x => ψ (F n x)) ν := by
    refine (integrable_const P).mono' (hψm n).aestronglyMeasurable ?_
    exact ae_of_all _ fun x => hψP _
  have hfi (n i) : Integrable (fun x => ψ (F n x) * D n i x) ν :=
    integrable_mul_bounded_test _ _ (hDi n i) (hψm n) P (fun x => hψP _)
  have hxi (n i) : Integrable (fun x => x i * (ψ (F n x) * D n i x)) ν := by
    have h := integrable_mul_bounded_test _ _ (hxiDi n i) (hψm n) P (fun x => hψP _)
    convert h using 1
    funext x
    ring
  have hgi (n i) : Integrable (fun x => deriv ψ (F n x) * D n i x ^ 2) ν :=
    integrable_mul_bounded_test _ _ (hDi2 n i) (hψ'm n) Q (fun x => hψQ _)
  have hddi (n i) : Integrable (fun x => ψ (F n x) * DD n i x) ν := by
    have hd : Integrable (DD n i) ν := hmp.integrable_comp_of_integrable
      (integrable_gramSoftMinSecond_single_gaussianMatrix (by omega) (n + 1) (by omega) ε hε i.1 i.2)
    exact integrable_mul_bounded_test _ _ hd (hψm n) P (fun x => hψP _)
  have hAgg : ∀ᵐ x ∂ν,
      Tendsto (fun n : ℕ => F n x) atTop (𝓝 (X x + ε)) ∧
      Tendsto (fun n : ℕ => ∑ i, D n i x ^ 2) atTop (𝓝 (4 * X x)) ∧
      Tendsto (fun n : ℕ => ∑ i, x i * D n i x) atTop (𝓝 (2 * X x)) := by
    have h := ae_tendsto_regularizedGram_softMin_aggregates_gaussianMatrix hr hrk ε hε
    rw [gaussianMatrix_eq_map_curry r k] at h
    filter_upwards [ae_of_ae_map e.measurable.aemeasurable h] with x hx
    refine ⟨hx.1.comp (tendsto_add_atTop_nat 1), ?_, ?_⟩
    · simpa only [henergy, Function.comp_def, G, X] using hx.2.1.comp (tendsto_add_atTop_nat 1)
    · simpa only [heuler, Function.comp_def, G, X] using hx.2.2.comp (tendsto_add_atTop_nat 1)
  have hCex : ∀ᵐ x ∂ν, ∃ L : ℝ, L ≤ b ∧
      Tendsto (fun n : ℕ => ∑ i, DD n i x) atTop (𝓝 L) := by
    have h := ae_exists_tendsto_gramSoftMinLaplacian_le_gaussianMatrix hr hrk ε hε
    rw [gaussianMatrix_eq_map_curry r k] at h
    filter_upwards [ae_of_ae_map e.measurable.aemeasurable h] with x hx
    obtain ⟨L, hL, ht⟩ := hx
    refine ⟨L, hL, ?_⟩
    simpa only [hlap, Function.comp_def, G] using ht.comp (tendsto_add_atTop_nat 1)
  let C' : ((Fin r × Fin k) → ℝ) → ℝ := fun x =>
    if h : ∃ L : ℝ, L ≤ b ∧ Tendsto (fun n : ℕ => ∑ i, DD n i x) atTop (𝓝 L)
      then Classical.choose h else 0
  have hClim : ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => ∑ i, DD n i x) atTop (𝓝 (C' x)) := by
    filter_upwards [hCex] with x hx
    simpa only [C', dif_pos hx] using (Classical.choose_spec hx).2
  have hC' : ∀ᵐ x ∂ν, C' x ≤ b := by
    filter_upwards [hCex] with x hx
    simpa only [C', dif_pos hx] using (Classical.choose_spec hx).1
  let bound : ((Fin r × Fin k) → ℝ) → ℝ := fun x => (4 * Q + 2 * P) * S x + |b| * P
  have hboundi : Integrable bound ν := (hSi.const_mul _).add (integrable_const _)
  have hweak := integral_nonneg_of_gaussian_coordinate_approximation
    F D DD (fun x => X x + ε) (fun x => 4 * X x) (fun x => 2 * X x) C' ψ hψ b (2 * k) P hP
    hψ0 (fun x => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hψP x))
    (fun n i x t => hasDerivAt_softMin_update hr (n + 1) (by omega) ε hε x i t)
    (fun n i x t => hasDerivAt_gradient_update hr (n + 1) (by omega) ε hε x i t)
    hψi hfi hxi hgi hddi
    (fun n => ae_of_all _ fun x => by
      rw [hlap]
      simpa only [Fintype.card_fin, gramSoftMinLaplacian] using
        sum_gramSoftMinSecond_single_le (n + 1) (by omega) hε (G x))
    (hAgg.mono fun x hx => hx.1) (hAgg.mono fun x hx => hx.2.1) (hAgg.mono fun x hx => hx.2.2)
    hClim hC' bound hboundi
    (fun n => ae_of_all _ fun x => norm_weak_expression_le hP hQ (hSnn x)
      (Finset.sum_nonneg fun i _ => sq_nonneg _) (hAs n x) (hBs n x) (hψP _) (hψQ _))
  have hXm : Measurable (fun H : Fin r → Fin k → ℝ => sigmaMin (Matrix.of H)ᵀ ^ 2) :=
    measurable_sigmaMin_transpose_sq
  have htest : Measurable (fun H : Fin r → Fin k → ℝ =>
      deriv ψ (sigmaMin (Matrix.of H)ᵀ ^ 2 + ε) * (4 * sigmaMin (Matrix.of H)ᵀ ^ 2) +
        (b - 2 * sigmaMin (Matrix.of H)ᵀ ^ 2) * ψ (sigmaMin (Matrix.of H)ᵀ ^ 2 + ε)) := by
    exact (((hψ.continuous_deriv le_rfl).measurable.comp (hXm.add_const ε)).mul
      (measurable_const.mul hXm)).add
      ((measurable_const.sub (measurable_const.mul hXm)).mul
        (hψ.continuous.measurable.comp (hXm.add_const ε)))
  rw [gaussianMatrix_eq_map_curry r k, integral_map e.measurable.aemeasurable htest.aestronglyMeasurable]
  exact hweak

/-- The smallest squared singular value of a wide standard Gaussian matrix
satisfies the sharp hard-edge weak differential inequality.
Source: operator rederivations, Section 5; atlas `wishart-lambda-min-tail`.
The proof uses actual regularized Gram derivatives, coordinate Stein identities,
and two dominated/one-sided limits. No density or approximation hypotheses remain.
The test may be any nonnegative smooth compactly supported function. -/
theorem integral_sigmaMin_transpose_sq_weak_nonneg_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
    0 ≤ ∫ G : Fin r → Fin k → ℝ,
      4 * sigmaMin (Matrix.of G)ᵀ ^ 2 * deriv ψ (sigmaMin (Matrix.of G)ᵀ ^ 2) +
        2 * ((k : ℝ) - r + 1 - sigmaMin (Matrix.of G)ᵀ ^ 2) *
          ψ (sigmaMin (Matrix.of G)ᵀ ^ 2) ∂(gaussianMatrix r k) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  obtain ⟨P, hP⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  obtain ⟨Q, hQ⟩ := (hψ1.continuous_deriv le_rfl).bounded_above_of_compact_support hψc.deriv
  have hP0 : 0 ≤ P := (norm_nonneg (ψ 0)).trans (hP 0)
  have hQ0 : 0 ≤ Q := (norm_nonneg (deriv ψ 0)).trans (hQ 0)
  let X : (Fin r → Fin k → ℝ) → ℝ := fun G => sigmaMin (Matrix.of G)ᵀ ^ 2
  let b : ℝ := 2 * ((k : ℝ) - r + 1)
  let bound : (Fin r → Fin k → ℝ) → ℝ :=
    fun G => (4 * Q + 2 * P) * frobSq (Matrix.of G) + |b| * P
  have hXi : Measurable X := measurable_sigmaMin_transpose_sq
  have hboundi : Integrable bound (gaussianMatrix r k) :=
    ((integrable_frobSq_gaussianMatrix r k).const_mul _).add (integrable_const _)
  have hweak := integral_nonneg_of_positive_translates (gaussianMatrix r k)
    X (fun G => 4 * X G) (fun G => 2 * X G) ψ (deriv ψ) hψ.continuous
    (hψ1.continuous_deriv le_rfl) b
    (fun ε _ => by
      exact (((hψ1.continuous_deriv le_rfl).measurable.comp (hXi.add_const ε)).mul
        (measurable_const.mul hXi)).add
        ((measurable_const.sub (measurable_const.mul hXi)).mul
          (hψ.continuous.measurable.comp (hXi.add_const ε))) |>.aestronglyMeasurable)
    bound hboundi
    (fun ε _ => ae_of_all _ fun G => by
      have hX : 0 ≤ X G := sq_nonneg _
      have hXs : X G ≤ frobSq (Matrix.of G) := sigmaMin_transpose_sq_le_frobSq _
      apply norm_weak_expression_le hP0 hQ0 (frobSq_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hXs (by norm_num)) ?_ (hP _) (hQ _)
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * X G)]
      exact mul_le_mul_of_nonneg_left hXs (by norm_num))
    (fun ε hε => integral_weak_shift_nonneg_gaussianMatrix hr hrk ε hε ψ hψ1 hψ0 P Q hP0 hQ0 hP hQ)
  have heq : (fun G : Fin r → Fin k → ℝ =>
      4 * sigmaMin (Matrix.of G)ᵀ ^ 2 * deriv ψ (sigmaMin (Matrix.of G)ᵀ ^ 2) +
        2 * ((k : ℝ) - r + 1 - sigmaMin (Matrix.of G)ᵀ ^ 2) * ψ (sigmaMin (Matrix.of G)ᵀ ^ 2))
      = (fun G => deriv ψ (X G) * (4 * X G) + (b - 2 * X G) * ψ (X G)) := by
    funext G
    dsimp only [X, b]
    ring
  rw [heq]
  exact hweak

/-- The scalar law of the squared smallest Gaussian singular value
satisfies the sharp weak inequality on the positive half-line.
Source: operator hard-edge proof and pushforward transport; atlas
`wishart-lambda-min-tail`. This is the direct input to the antitone
Gamma-weighted density theorem. -/
theorem integral_sigmaMin_transpose_sq_law_weak_nonneg_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
    0 ≤ ∫ x in Ioi (0 : ℝ), 4 * x * deriv ψ x + 2 * ((k : ℝ) - r + 1 - x) * ψ x
      ∂((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2)) := by
  have hm : Measurable (fun G : Fin r → Fin k → ℝ => sigmaMin (Matrix.of G)ᵀ ^ 2) :=
    measurable_sigmaMin_transpose_sq
  have hpos : ∀ᵐ x ∂((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2)),
      x ∈ Ioi (0 : ℝ) :=
    (ae_map_iff hm.aemeasurable measurableSet_Ioi).2
      (ae_sigmaMin_transpose_sq_pos_gaussianMatrix hr hrk)
  have hφ : Measurable (fun x : ℝ => 4 * x * deriv ψ x + 2 * ((k : ℝ) - r + 1 - x) * ψ x) := by
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    exact ((measurable_const.mul measurable_id).mul (hψ1.continuous_deriv le_rfl).measurable).add
      ((measurable_const.mul (measurable_const.sub measurable_id)).mul hψ.continuous.measurable)
  rw [Measure.restrict_eq_self_of_ae_mem hpos, integral_map hm.aemeasurable hφ.aestronglyMeasurable]
  exact integral_sigmaMin_transpose_sq_weak_nonneg_gaussianMatrix hr hrk ψ hψ hψc hψ0

end NLAlib
