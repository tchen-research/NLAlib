import NLAlib.Gaussian.Concentration.Stein
import NLAlib.Gaussian.InverseMoments.RegularizedApproximation
import NLAlib.Matrix.UnshiftedGramSoftMin
import NLAlib.Matrix.GramSoftMinMeasurable
import NLAlib.Matrix.CoordinateUpdates
import NLAlib.Gaussian.InverseMoments.CutoffIntegrability
import NLAlib.Gaussian.InverseMoments.CutoffDerivativeIntegrability
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The unshifted Gaussian hard-edge weak inequality

The finite inverse-power Gram probes already satisfy the sharp hard-edge
Laplacian bound. Positive-support scalar cutoffs make their coordinate
Stein fields globally differentiable even on singular matrices. Ordinary
dominated convergence of value and gradient energy completes the proof.

Source: unshifted operator improvement; atlas `wishart-lambda-min-tail`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.L2Operator

namespace NLAlib

private theorem ae_posDef_gram {r k : ℕ} (hrk : r ≤ k) :
    ∀ᵐ G ∂(gaussianMatrix r k), (Matrix.of G * (Matrix.of G)ᵀ).PosDef := by
  filter_upwards [gaussianMatrix_ae_isUnit_mul_transpose hrk] with G hG
  have hp : (Matrix.of G * (Matrix.of G)ᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)
  exact hp.posDef_iff_isUnit.mpr hG

private theorem measurable_minSq {r k : ℕ} :
    Measurable (fun G : Fin r → Fin k → ℝ => sigmaMin (Matrix.of G)ᵀ ^ 2) := by
  convert measurable_specNorm_inv_self_mul_transpose.inv using 1
  funext G
  change sigmaMin (Matrix.of G)ᵀ ^ 2 = (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)⁻¹
  rw [specNorm_inv_self_mul_transpose_eq, one_div, inv_inv]

/-- The unshifted Gram inverse-power probes and their gradient energy
converge almost surely to the exact smallest squared Gaussian singular
value and four times that value. Source: Gaussian full rank, polynomial
simple spectrum, and inverse-power first-order limits;
atlas `wishart-lambda-min-tail` (unshifted approximation helper). -/
theorem ae_tendsto_unshiftedGram_softMin_energy_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    ∀ᵐ G ∂(gaussianMatrix r k),
      Tendsto (fun n : ℕ => inversePowerSoftMin n (regularizedGram 0 (Matrix.of G)))
        atTop (𝓝 (sigmaMin (Matrix.of G)ᵀ ^ 2)) ∧
      Tendsto (fun n : ℕ => frobSq (gramSoftMinGradient n 0 (Matrix.of G)))
        atTop (𝓝 (4 * sigmaMin (Matrix.of G)ᵀ ^ 2)) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  filter_upwards [gaussianMatrix_ae_isUnit_mul_transpose hrk,
    ae_charpoly_separable_self_mul_transpose_gaussianMatrix hrk] with G hunit hsep
  have hW : (Matrix.of G * (Matrix.of G)ᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)
  have hpd : (regularizedGram 0 (Matrix.of G)).PosDef := by
    simpa only [regularizedGram, zero_smul, add_zero] using hW.posDef_iff_isUnit.mpr hunit
  let b := hpd.inv.isHermitian.eigenvalues
  let U := star hpd.inv.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix (Fin r) (Fin r) ℝ) U
  have hdiag : φ (Matrix.of G * (Matrix.of G)ᵀ) = Matrix.diagonal (fun i => (b i)⁻¹) := by
    simpa only [sub_zero] using regularizedGram_inv_basis_conj_eq 0 (Matrix.of G) hpd
  have hchar : (φ (Matrix.of G * (Matrix.of G)ᵀ)).charpoly =
      (Matrix.of G * (Matrix.of G)ᵀ).charpoly := by
    dsimp only [φ]
    rw [Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hsep' : (Matrix.diagonal (fun i => (b i)⁻¹)).charpoly.Separable := by
    rw [← hdiag, hchar]
    exact hsep
  rw [Matrix.charpoly_diagonal] at hsep'
  have hinvinj := Polynomial.separable_prod_X_sub_C_iff.1 hsep'
  have hbinj : Function.Injective b := by
    intro i j hij
    apply hinvinj
    exact congrArg Inv.inv hij
  obtain ⟨i₀, hi₀⟩ := (IsGreatest.pi_norm b).1
  change ‖b i₀‖ = ‖b‖ at hi₀
  have hle (i : Fin r) : b i ≤ b i₀ := by
    have hn := norm_le_pi_norm b i
    have hb (j : Fin r) : 0 ≤ b j := (hpd.inv.eigenvalues_pos j).le
    rw [← hi₀, Real.norm_of_nonneg (hb i), Real.norm_of_nonneg (hb i₀)] at hn
    exact hn
  have hmax (i : Fin r) (hi : i ≠ i₀) : b i < b i₀ :=
    lt_of_le_of_ne (hle i) (fun h => hi (hbinj h))
  have hX := sigmaMin_transpose_sq_eq_inv_inverse_eigenvalue_sub 0 (Matrix.of G) hpd i₀ hle
  simp only [sub_zero] at hX
  obtain ⟨hF, hA, _⟩ :=
    tendsto_regularizedGram_softMin_aggregates_of_unique_max 0 (Matrix.of G) hpd i₀ hmax
  simp only [sub_zero] at hA
  rw [← hX] at hF hA
  exact ⟨hF, hA⟩

private theorem integral_cutoff_weak_nonneg_of_coordinate_stein
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (D DD : ι → (ι → ℝ) → ℝ)
    (ψ : ℝ → ℝ) (b : ℝ) (hψ0 : ∀ t, 0 ≤ ψ t)
    (hupdate : ∀ i x t, HasDerivAt (fun y =>
      ψ (F (Function.update x i y)) * D i (Function.update x i y))
      (deriv ψ (F (Function.update x i t)) * D i (Function.update x i t) ^ 2 +
        ψ (F (Function.update x i t)) * DD i (Function.update x i t)) t)
    (hVi : ∀ i, Integrable (fun x => ψ (F x) * D i x)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hxVi : ∀ i, Integrable (fun x => x i * (ψ (F x) * D i x))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdVi : ∀ i, Integrable (fun x => deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hψi : Integrable (fun x => ψ (F x)) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hAi : Integrable (fun x => deriv ψ (F x) * (∑ i, D i x ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hEuler : ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1), (∑ i, x i * D i x) = 2 * F x)
    (hLap : ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1), (∑ i, DD i x) ≤ b) :
    0 ≤ ∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) + (b - 2 * F x) * ψ (F x)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let μ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  have hcoord (i : ι) : (∫ x, x i * (ψ (F x) * D i x) ∂μ) =
      ∫ x, deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x ∂μ :=
    integral_coordinate_mul_eq_integral_gaussian_of_hasDerivAt_update
      (fun x => ψ (F x) * D i x)
      (fun x => deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x)
      i (hupdate i) (hVi i) (hxVi i) (hdVi i)
  have hsumI : Integrable (fun x => ∑ i, (deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x)) μ :=
    integrable_finsetSum _ (fun i _ => hdVi i)
  have hCi : Integrable (fun x => ψ (F x) * (∑ i, DD i x)) μ := by
    convert! hsumI.sub hAi using 1
    funext x
    simp only [Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hBi : Integrable (fun x => ψ (F x) * (∑ i, x i * D i x)) μ := by
    have h := integrable_finsetSum Finset.univ (fun i _ => hxVi i)
    convert! h using 1
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hStein : (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) ∂μ) +
      (∫ x, ψ (F x) * (∑ i, DD i x) ∂μ) =
      ∫ x, ψ (F x) * (∑ i, x i * D i x) ∂μ := by
    rw [← integral_add hAi hCi]
    calc _ = ∫ x, ∑ i, (deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            change deriv ψ (F x) * (∑ i, D i x ^ 2) + ψ (F x) * (∑ i, DD i x) =
              ∑ i, (deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x)
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = ∑ i, ∫ x, deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x ∂μ :=
          integral_finsetSum _ (fun i _ => hdVi i)
      _ = ∑ i, ∫ x, x i * (ψ (F x) * D i x) ∂μ :=
          Finset.sum_congr rfl fun i _ => (hcoord i).symm
      _ = ∫ x, ∑ i, x i * (ψ (F x) * D i x) ∂μ :=
          (integral_finsetSum _ (fun i _ => hxVi i)).symm
      _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            change (∑ i, x i * (ψ (F x) * D i x)) = ψ (F x) * (∑ i, x i * D i x)
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
  have hCL : (∫ x, ψ (F x) * (∑ i, DD i x) ∂μ) ≤ b * ∫ x, ψ (F x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hCi (hψi.const_mul b)
    filter_upwards [hLap] with x hx
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hx (hψ0 _)
  have hleft : (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) + (b - 2 * F x) * ψ (F x) ∂μ) =
      (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) ∂μ) + b * (∫ x, ψ (F x) ∂μ) -
        ∫ x, ψ (F x) * (∑ i, x i * D i x) ∂μ := by
    have heq : (fun x => deriv ψ (F x) * (∑ i, D i x ^ 2) + (b - 2 * F x) * ψ (F x))
        =ᵐ[μ] (fun x => (deriv ψ (F x) * (∑ i, D i x ^ 2) + b * ψ (F x)) -
          ψ (F x) * (∑ i, x i * D i x)) := by
      filter_upwards [hEuler] with x hx
      rw [hx]
      ring
    rw [integral_congr_ae heq]
    rw [integral_sub (μ := μ)
      (f := fun x => deriv ψ (F x) * (∑ i, D i x ^ 2) + b * ψ (F x))
      (g := fun x => ψ (F x) * (∑ i, x i * D i x)) (hAi.add (hψi.const_mul b)) hBi]
    rw [integral_add (μ := μ)
      (f := fun x => deriv ψ (F x) * (∑ i, D i x ^ 2))
      (g := fun x => b * ψ (F x)) hAi (hψi.const_mul b), integral_const_mul]
  rw [hleft]
  linarith

private lemma norm_cutoff_energy_le (ψ : ℝ → ℝ) (B Q y A : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (_hy : 0 ≤ y) (hA : 0 ≤ A) (hAy : A ≤ 4 * y)
    (hψ' : ∀ t, ‖deriv ψ t‖ ≤ Q) (hzero : ∀ t, B < t → deriv ψ t = 0) :
    ‖deriv ψ y * A‖ ≤ 4 * B * Q := by
  by_cases h : y ≤ B
  · rw [norm_mul, Real.norm_of_nonneg hA]
    have hAB : A ≤ 4 * B := by linarith
    have hm := mul_le_mul (hψ' y) hAB hA hQ
    nlinarith
  · rw [hzero y (lt_of_not_ge h), zero_mul, norm_zero]
    positivity

private lemma norm_cutoff_weak_le (ψ : ℝ → ℝ) (B P Q y A b : ℝ)
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hy : 0 ≤ y) (hA : 0 ≤ A) (hAy : A ≤ 4 * y)
    (hψ : ∀ t, ‖ψ t‖ ≤ P) (hψ' : ∀ t, ‖deriv ψ t‖ ≤ Q)
    (hzero : ∀ t, B < t → ψ t = 0 ∧ deriv ψ t = 0) :
    ‖deriv ψ y * A + (b - 2 * y) * ψ y‖ ≤ 4 * B * Q + (|b| + 2 * B) * P := by
  by_cases h : y ≤ B
  · have hE := norm_cutoff_energy_le ψ B Q y A hB hQ hy hA hAy hψ'
      (fun t ht => (hzero t ht).2)
    have hsub : |b - 2 * y| ≤ |b| + 2 * B := by
      have hh := abs_sub b (2 * y)
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * y)] at hh
      linarith
    have hT : ‖(b - 2 * y) * ψ y‖ ≤ (|b| + 2 * B) * P := by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul hsub (hψ y) (norm_nonneg _) (by positivity)
    exact (norm_add_le _ _).trans (add_le_add hE hT)
  · obtain ⟨hp, hd⟩ := hzero y (lt_of_not_ge h)
    rw [hp, hd, zero_mul, mul_zero, zero_add, norm_zero]
    positivity

private theorem hasDerivAt_unshifted_cutoff_update
    {r k : ℕ} (hr : 1 ≤ r) (n : ℕ) (hn : 0 < n)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioi (0 : ℝ))
    (x : Fin r × Fin k → ℝ) (i : Fin r × Fin k) (t : ℝ) :
    HasDerivAt (fun y : ℝ =>
      let H := Matrix.of (fun a b => Function.update x i y (a, b))
      ψ (inversePowerSoftMin n (H * Hᵀ)) * gramSoftMinGradient n 0 H i.1 i.2)
      (let H := Matrix.of (fun a b => Function.update x i t (a, b))
      deriv ψ (inversePowerSoftMin n (H * Hᵀ)) * gramSoftMinGradient n 0 H i.1 i.2 ^ 2 +
        ψ (inversePowerSoftMin n (H * Hᵀ)) * gramSoftMinSecond n 0 H (Matrix.single i.1 i.2 1)) t := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let H : Matrix (Fin r) (Fin k) ℝ := Matrix.of (fun a b => Function.update x i t (a, b))
  let E : Matrix (Fin r) (Fin k) ℝ := Matrix.single i.1 i.2 1
  have heq (y : ℝ) : Matrix.of (fun a b => Function.update x i y (a, b)) = H + (y - t) • E := by
    have hh := matrixOf_curry_update_eq_add_single (Function.update x i t) i.1 i.2 y
    simpa only [Prod.mk.eta, Function.update_idem, Function.update_self] using hh
  have hh := (hasDerivAt_test_mul_unshiftedGramGradient_single n hn ψ hψ hψc hψs H i.1 i.2).comp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  simpa only [Function.comp_def, heq, sub_self, mul_one, id_eq, zero_smul, add_zero, E] using hh

/-- The exact Gaussian hard-edge weak inequality follows from the sharp
finite unshifted inverse-power probes and ordinary dominated convergence.
Source: the unshifted finite-operator refinement; atlas
`wishart-lambda-min-tail`. The cutoff Stein fields are globally differentiable,
including singular inputs, and only value/gradient-energy limits are used. -/
theorem integral_sigmaMin_transpose_sq_unshifted_weak_nonneg_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioi (0 : ℝ)) (hψ0 : ∀ x, 0 ≤ ψ x) :
    0 ≤ ∫ G : Fin r → Fin k → ℝ,
      4 * sigmaMin (Matrix.of G)ᵀ ^ 2 * deriv ψ (sigmaMin (Matrix.of G)ᵀ ^ 2) +
        2 * ((k : ℝ) - r + 1 - sigmaMin (Matrix.of G)ᵀ ^ 2) *
          ψ (sigmaMin (Matrix.of G)ᵀ ^ 2) ∂(gaussianMatrix r k) := by
  classical
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let ν : Measure ((Fin r × Fin k) → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let e := MeasurableEquiv.curry (Fin r) (Fin k) ℝ
  have hmp : MeasurePreserving e ν (gaussianMatrix r k) :=
    ⟨e.measurable, (gaussianMatrix_eq_map_curry r k).symm⟩
  let G : ((Fin r × Fin k) → ℝ) → Matrix (Fin r) (Fin k) ℝ := fun x => Matrix.of (e x)
  let X : ((Fin r × Fin k) → ℝ) → ℝ := fun x => sigmaMin (G x)ᵀ ^ 2
  let F : ℕ → ((Fin r × Fin k) → ℝ) → ℝ :=
    fun n x => inversePowerSoftMin (n + 1) (G x * (G x)ᵀ)
  let D : ℕ → (Fin r × Fin k) → ((Fin r × Fin k) → ℝ) → ℝ :=
    fun n i x => gramSoftMinGradient (n + 1) 0 (G x) i.1 i.2
  let DD : ℕ → (Fin r × Fin k) → ((Fin r × Fin k) → ℝ) → ℝ :=
    fun n i x => gramSoftMinSecond (n + 1) 0 (G x) (Matrix.single i.1 i.2 1)
  let A : ℕ → ((Fin r × Fin k) → ℝ) → ℝ := fun n x => ∑ i, D n i x ^ 2
  let b : ℝ := 2 * ((k : ℝ) - r + 1)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  obtain ⟨P, hP⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  obtain ⟨Q, hQ⟩ := (hψ1.continuous_deriv le_rfl).bounded_above_of_compact_support hψc.deriv
  have hP0 : 0 ≤ P := (norm_nonneg (ψ 0)).trans (hP 0)
  have hQ0 : 0 ≤ Q := (norm_nonneg (deriv ψ 0)).trans (hQ 0)
  obtain ⟨B₁, hB₁⟩ := hψc.isCompact.bddAbove
  obtain ⟨B₂, hB₂⟩ := hψc.deriv.isCompact.bddAbove
  let B : ℝ := max (max B₁ B₂) 0 + 1
  have hB : 0 ≤ B := by dsimp only [B]; linarith [le_max_right (max B₁ B₂) 0]
  have hzero : ∀ t, B < t → ψ t = 0 ∧ deriv ψ t = 0 := by
    intro t ht
    constructor
    · apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hh := hB₁ hs
      dsimp only [B] at ht
      linarith [le_max_left B₁ B₂, le_max_left (max B₁ B₂) 0]
    · apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hh := hB₂ hs
      dsimp only [B] at ht
      linarith [le_max_right B₁ B₂, le_max_left (max B₁ B₂) 0]
  have hFm (n) : Measurable (F n) := by
    simpa only [regularizedGram_zero, Function.comp_def, F, G] using
      (measurable_inversePowerSoftMin_regularizedGram (n + 1) 0).comp e.measurable
  have hDm (n i) : Measurable (D n i) :=
    (measurable_gramSoftMinGradient_entry (n + 1) 0 i.1 i.2).comp e.measurable
  have hAm (n) : Measurable (A n) :=
    Finset.measurable_sum _ (fun i _ => (hDm n i).pow_const 2)
  have hψm (n) : Measurable (fun x => ψ (F n x)) := hψ.continuous.measurable.comp (hFm n)
  have hψ'm (n) : Measurable (fun x => deriv ψ (F n x)) :=
    (hψ1.continuous_deriv le_rfl).measurable.comp (hFm n)
  have hPD : ∀ᵐ x ∂ν, (G x * (G x)ᵀ).PosDef := by
    have hh := ae_posDef_gram hrk
    rw [gaussianMatrix_eq_map_curry r k] at hh
    exact ae_of_ae_map e.measurable.aemeasurable hh
  have hAn (n x) : 0 ≤ A n x := Finset.sum_nonneg fun i _ => sq_nonneg _
  have henergy (n x) : A n x = frobSq (gramSoftMinGradient (n + 1) 0 (G x)) := by
    simp only [A, Fintype.sum_prod_type, D, frobSq, frobInner, ← sq]
  have hAineq (n) : ∀ᵐ x ∂ν, 0 ≤ F n x ∧ A n x ≤ 4 * F n x := by
    filter_upwards [hPD] with x hx
    refine ⟨Real.rpow_nonneg (trace_pow_pos_of_posDef hx.inv _).le _, ?_⟩
    rw [henergy]
    exact frobSq_gramSoftMinGradient_unshifted_le (n + 1) (by omega) (G x) hx
  have hψi (n) : Integrable (fun x => ψ (F n x)) ν := by
    exact (integrable_const P).mono' (hψm n).aestronglyMeasurable (ae_of_all _ fun x => hP _)
  have hAi (n) : Integrable (fun x => deriv ψ (F n x) * A n x) ν := by
    refine (integrable_const (4 * B * Q)).mono' ((hψ'm n).mul (hAm n)).aestronglyMeasurable ?_
    filter_upwards [hAineq n] with x hx
    exact norm_cutoff_energy_le ψ B Q (F n x) (A n x) hB hQ0 hx.1 (hAn n x) hx.2 hQ
      (fun t ht => (hzero t ht).2)
  have hVi (n i) : Integrable (fun x => ψ (F n x) * D n i x) ν :=
    hmp.integrable_comp_of_integrable
      (integrable_test_mul_unshiftedGramGradient_single_gaussianMatrix (by omega)
        (n + 1) (by omega) ψ hψ hψc hψs i.1 i.2)
  have hxVi (n i) : Integrable (fun x => x i * (ψ (F n x) * D n i x)) ν :=
    hmp.integrable_comp_of_integrable
      (integrable_coordinate_mul_test_mul_unshiftedGramGradient_single_gaussianMatrix (by omega)
        (n + 1) (by omega) ψ hψ hψc hψs i.1 i.2)
  have hdVi (n i) : Integrable (fun x => deriv ψ (F n x) * D n i x ^ 2 + ψ (F n x) * DD n i x) ν :=
    hmp.integrable_comp_of_integrable
      (integrable_test_unshiftedGramVectorFieldDerivative_single_gaussianMatrix (by omega)
        (n + 1) (by omega) ψ hψ hψc hψs i.1 i.2)
  have hEuler (n) : ∀ᵐ x ∂ν, (∑ i, x i * D n i x) = 2 * F n x := by
    filter_upwards [hPD] with x hx
    have he : (∑ i, x i * D n i x) = frobInner (G x) (gramSoftMinGradient (n + 1) 0 (G x)) := by
      simp only [Fintype.sum_prod_type, D, frobInner, G, e, MeasurableEquiv.curry_apply, Matrix.of_apply]
    rw [he]
    exact frobInner_gramSoftMinGradient_unshifted_eq (n + 1) (G x) hx
  have hLap (n) : ∀ᵐ x ∂ν, (∑ i, DD n i x) ≤ b := by
    filter_upwards [hPD] with x hx
    have hgap : 0 ≤ (Fintype.card (Fin k) : ℝ) - Fintype.card (Fin r) + 1 := by
      have hle : (r : ℝ) ≤ k := by exact_mod_cast hrk
      simp only [Fintype.card_fin]
      linarith
    simpa only [DD, Fintype.sum_prod_type, gramSoftMinLaplacian, Fintype.card_fin] using
      gramSoftMinLaplacian_unshifted_le (n + 1) (by omega) (G x) hx hgap
  let L : ℕ → ((Fin r × Fin k) → ℝ) → ℝ := fun n x =>
    deriv ψ (F n x) * A n x + (b - 2 * F n x) * ψ (F n x)
  have hLn (n) : 0 ≤ ∫ x, L n x ∂ν :=
    integral_cutoff_weak_nonneg_of_coordinate_stein (F n) (D n) (DD n) ψ b hψ0
      (fun i x t => hasDerivAt_unshifted_cutoff_update hr (n + 1) (by omega) ψ hψ hψc hψs x i t)
      (hVi n) (hxVi n) (hdVi n) (hψi n) (hAi n) (hEuler n) (hLap n)
  let C : ℝ := 4 * B * Q + (|b| + 2 * B) * P
  have hbound (n) : ∀ᵐ x ∂ν, ‖L n x‖ ≤ C := by
    filter_upwards [hAineq n] with x hx
    exact norm_cutoff_weak_le ψ B P Q (F n x) (A n x) b hB hP0 hQ0 hx.1 (hAn n x) hx.2 hP hQ hzero
  have hAgg : ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => F n x) atTop (𝓝 (X x)) ∧
      Tendsto (fun n : ℕ => A n x) atTop (𝓝 (4 * X x)) := by
    have hh := ae_tendsto_unshiftedGram_softMin_energy_gaussianMatrix hr hrk
    rw [gaussianMatrix_eq_map_curry r k] at hh
    filter_upwards [ae_of_ae_map e.measurable.aemeasurable hh] with x hx
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_def, regularizedGram_zero, F, G, X] using hx.1.comp (tendsto_add_atTop_nat 1)
    · simpa only [Function.comp_def, henergy, G, X] using hx.2.comp (tendsto_add_atTop_nat 1)
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => L n x) atTop
      (𝓝 (deriv ψ (X x) * (4 * X x) + (b - 2 * X x) * ψ (X x))) := by
    filter_upwards [hAgg] with x hx
    exact (((hψ1.continuous_deriv le_rfl).continuousAt.tendsto.comp hx.1).mul hx.2).add
      ((tendsto_const_nhds.sub (hx.1.const_mul 2)).mul (hψ.continuous.continuousAt.tendsto.comp hx.1))
  have hInt := tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (((hψ'm n).mul (hAm n)).add
      ((measurable_const.sub (measurable_const.mul (hFm n))).mul (hψm n))).aestronglyMeasurable)
    (integrable_const C) hbound hlim
  have hweak := ge_of_tendsto hInt (Eventually.of_forall hLn)
  have hXm : Measurable (fun H : Fin r → Fin k → ℝ => sigmaMin (Matrix.of H)ᵀ ^ 2) := measurable_minSq
  have hφ : Measurable (fun H : Fin r → Fin k → ℝ =>
      deriv ψ (sigmaMin (Matrix.of H)ᵀ ^ 2) * (4 * sigmaMin (Matrix.of H)ᵀ ^ 2) +
        (b - 2 * sigmaMin (Matrix.of H)ᵀ ^ 2) * ψ (sigmaMin (Matrix.of H)ᵀ ^ 2)) :=
    (((hψ1.continuous_deriv le_rfl).measurable.comp hXm).mul (measurable_const.mul hXm)).add
      ((measurable_const.sub (measurable_const.mul hXm)).mul (hψ.continuous.measurable.comp hXm))
  have heq : (fun H : Fin r → Fin k → ℝ =>
      4 * sigmaMin (Matrix.of H)ᵀ ^ 2 * deriv ψ (sigmaMin (Matrix.of H)ᵀ ^ 2) +
        2 * ((k : ℝ) - r + 1 - sigmaMin (Matrix.of H)ᵀ ^ 2) * ψ (sigmaMin (Matrix.of H)ᵀ ^ 2)) =
      (fun H => deriv ψ (sigmaMin (Matrix.of H)ᵀ ^ 2) * (4 * sigmaMin (Matrix.of H)ᵀ ^ 2) +
        (b - 2 * sigmaMin (Matrix.of H)ᵀ ^ 2) * ψ (sigmaMin (Matrix.of H)ᵀ ^ 2)) := by
    funext H
    dsimp only [b]
    ring
  rw [heq, gaussianMatrix_eq_map_curry r k, integral_map e.measurable.aemeasurable hφ.aestronglyMeasurable]
  exact hweak

/-- The scalar squared-smallest-singular-value law satisfies the sharp
hard-edge weak inequality by the unshifted finite-probe route.
Source: the user's finite operator refinement and scalar-law transport;
atlas `wishart-lambda-min-tail`. This proof uses no regularization limit,
Laplacian limit, or one-sided Fatou argument. -/
theorem integral_sigmaMin_transpose_sq_law_unshifted_weak_nonneg_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioi (0 : ℝ)) (hψ0 : ∀ x, 0 ≤ ψ x) :
    0 ≤ ∫ x in Ioi (0 : ℝ), 4 * x * deriv ψ x + 2 * ((k : ℝ) - r + 1 - x) * ψ x
      ∂((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2)) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hm : Measurable (fun G : Fin r → Fin k → ℝ => sigmaMin (Matrix.of G)ᵀ ^ 2) := measurable_minSq
  have hposG : ∀ᵐ G ∂(gaussianMatrix r k), 0 < sigmaMin (Matrix.of G)ᵀ ^ 2 := by
    filter_upwards [ae_posDef_gram hrk] with G hG
    have hpos : 0 < inversePowerSoftMin 1 (Matrix.of G * (Matrix.of G)ᵀ) :=
      Real.rpow_pos_of_pos (trace_pow_pos_of_posDef hG.inv 1) _
    exact hpos.trans_le (inversePowerSoftMin_gram_le_sigmaMin_sq 1 (by omega) (Matrix.of G))
  have hpos : ∀ᵐ x ∂((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2)),
      x ∈ Ioi (0 : ℝ) := (ae_map_iff hm.aemeasurable measurableSet_Ioi).2 hposG
  have hφ : Measurable (fun x : ℝ => 4 * x * deriv ψ x + 2 * ((k : ℝ) - r + 1 - x) * ψ x) := by
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    exact ((measurable_const.mul measurable_id).mul (hψ1.continuous_deriv le_rfl).measurable).add
      ((measurable_const.mul (measurable_const.sub measurable_id)).mul hψ.continuous.measurable)
  rw [Measure.restrict_eq_self_of_ae_mem hpos, integral_map hm.aemeasurable hφ.aestronglyMeasurable]
  exact integral_sigmaMin_transpose_sq_unshifted_weak_nonneg_gaussianMatrix hr hrk ψ hψ hψc hψs hψ0

end NLAlib
