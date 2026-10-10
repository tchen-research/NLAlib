import NLAlib.LowRank.GaussianNystrom
import NLAlib.LowRank.RawNystromBridge
import NLAlib.Gaussian.SketchRank
import NLAlib.Matrix.SvdBlocks
import NLAlib.Matrix.Measurable
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Gaussian compression of an independent random orthonormal frame

An independently sampled Gaussian second sketch has full rank on a measurable random
orthonormal frame. The rank property follows from the fixed-frame Gaussian block law and
Fubini; it is not an assumed moment or full-rank certificate. The first random input may
have any law. Atlas: `gn-expected-error`, `gaussian-conditioning`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- Orthonormality of an entrywise measurable finite matrix family is a measurable event.
Atlas `gn-expected-error` (random-frame measurability helper). -/
theorem measurableSet_hasOrthonormalCols_of_entries
    {α m q : Type*} [MeasurableSpace α] [Fintype m] [Fintype q] [DecidableEq q]
    {Q : α → Matrix m q ℝ} (hQ : ∀ i j, Measurable fun x => Q x i j) :
    MeasurableSet {x | HasOrthonormalCols (Q x)} := by
  have hGram := measurable_mul_entry_of (fun i j => hQ j i) hQ
  have hEq : {x | HasOrthonormalCols (Q x)} =
      ⋂ i, ⋂ j, {x | ((Q x)ᵀ * Q x) i j = (1 : Matrix q q ℝ) i j} := by
    ext x
    simp only [HasOrthonormalCols, Matrix.ext_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hEq]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    measurableSet_eq_fun (hGram i j) measurable_const

private theorem measurableSet_compression_isUnit
    {α : Type*} [MeasurableSpace α] {m q s : ℕ}
    (Q : α → Matrix (Fin m) (Fin q) ℝ)
    (hQ : ∀ i j, Measurable fun x => Q x i j) :
    MeasurableSet {p : α × (Fin m → Fin s → ℝ) |
      IsUnit (((Matrix.of p.2)ᵀ * Q p.1)ᵀ * ((Matrix.of p.2)ᵀ * Q p.1))} := by
  have hΨ : ∀ i j, Measurable fun p : α × (Fin m → Fin s → ℝ) => (Matrix.of p.2)ᵀ i j := by
    intro i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have hQ' : ∀ i j, Measurable fun p : α × (Fin m → Fin s → ℝ) => Q p.1 i j :=
    fun i j => (hQ i j).comp measurable_fst
  have hW := measurable_mul_entry_of hΨ hQ'
  have hGram := measurable_mul_entry_of (fun i j => hW j i) hW
  have hArray : Measurable fun p : α × (Fin m → Fin s → ℝ) =>
      (fun i j => (((Matrix.of p.2)ᵀ * Q p.1)ᵀ * ((Matrix.of p.2)ᵀ * Q p.1)) i j) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hGram i j
  have hdet : Measurable fun p : α × (Fin m → Fin s → ℝ) =>
      (((Matrix.of p.2)ᵀ * Q p.1)ᵀ * ((Matrix.of p.2)ᵀ * Q p.1)).det := by
    have hc : Continuous fun G : Fin q → Fin q → ℝ => (Matrix.of G).det :=
      continuous_id.matrix_det
    exact hc.measurable.comp hArray
  simpa only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Set.compl_ofPred] using
    (measurableSet_eq_fun hdet measurable_const).compl

/-- **Independent Gaussian sketch has full rank on a random orthonormal frame.**
Let `X` have any law, let the Gaussian `m×s` array `Ψ` be independent of `X`, and let
`Qf(X)` be a measurable frame with a.s. orthonormal `q` columns. If `q≤s`, then
`(ΨᵀQf(X))ᵀ(ΨᵀQf(X))` is invertible almost surely. The statement includes `q=0`.
HMT 2011, §10.2 and Proposition A.5; atlas `gn-expected-error`, `gaussian-conditioning`. -/
theorem ae_isUnit_gaussian_compression_of_indep
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m q s : ℕ}
    (X : Ω → α) (hX : AEMeasurable X μ) (Ψ : Ω → Fin m → Fin s → ℝ)
    (hΨ : μ.map Ψ = gaussianMatrix m s) (hind : IndepFun X Ψ μ)
    (Qf : α → Matrix (Fin m) (Fin q) ℝ)
    (hQf : ∀ i j, Measurable fun x => Qf x i j)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Qf (X ω))) (hqs : q ≤ s) :
    ∀ᵐ ω ∂μ, IsUnit (((Matrix.of (Ψ ω))ᵀ * Qf (X ω))ᵀ *
      ((Matrix.of (Ψ ω))ᵀ * Qf (X ω))) := by
  have hYm : AEMeasurable Ψ μ := aemeasurable_of_map_eq_gaussianMatrix hΨ
  have hLeft : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX
  have hFrame : ∀ᵐ x ∂μ.map X, HasOrthonormalCols (Qf x) :=
    (ae_map_iff hX (measurableSet_hasOrthonormalCols_of_entries hQf)).2 hQo
  have hProd : ∀ᵐ p ∂(μ.map X).prod (gaussianMatrix m s),
      IsUnit (((Matrix.of p.2)ᵀ * Qf p.1)ᵀ * ((Matrix.of p.2)ᵀ * Qf p.1)) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_compression_isUnit Qf hQf)).2
    filter_upwards [hFrame] with x hx
    have hFixed := ae_isUnit_block (μ := gaussianMatrix m s)
      (Ω := fun G : Fin m → Fin s → ℝ => G) (by simp) (Qf x) hx hqs
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hFixed
  have hLaw : μ.map (fun ω => (X ω, Ψ ω)) = (μ.map X).prod (gaussianMatrix m s) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX hYm).1 hind, hΨ]
  have hMap : ∀ᵐ p ∂μ.map (fun ω => (X ω, Ψ ω)),
      IsUnit (((Matrix.of p.2)ᵀ * Qf p.1)ᵀ * ((Matrix.of p.2)ᵀ * Qf p.1)) := by
    rw [hLaw]
    exact hProd
  exact ae_of_ae_map (hX.prodMk hYm) hMap

/-- The raw Moore–Penrose Nyström formula has the rank-sensitive expected Frobenius
bound when an entrywise measurable exact-rank orthonormal frame for the first sketch is
supplied. Gaussian laws discharge all moments and injectivity of the independent second
sketch. The frame/rank hypotheses are explicit; this theorem does not construct that
frame from an arbitrary input matrix. Tropp–Webber 2023, Theorem 5.1;
atlas `gn-expected-error`. -/
theorem integrable_and_integral_frobSq_rawGeneralizedNystrom_le_of_exact_rank_frame
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {m n k r r' t s q : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t) (hqs : q + 2 ≤ s) (hq : 1 ≤ q)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ) (Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t)
    (hΨ : μ.map (fun ω => Matrix.of.symm (Ψ ω)) = gaussianMatrix m s)
    (hind : IndepFun (fun ω => Matrix.of.symm (Ω ω)) (fun ω => Matrix.of.symm (Ψ ω)) μ)
    (Qf : (Fin n → Fin t → ℝ) → Matrix (Fin m) (Fin q) ℝ)
    (hQf : ∀ i j, Measurable fun x => Qf x i j)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Qf (Matrix.of.symm (Ω ω))))
    (hQr : ∀ᵐ ω ∂μ, Qf (Matrix.of.symm (Ω ω)) *
      ((Qf (Matrix.of.symm (Ω ω)))ᵀ * (A * Ω ω)) = A * Ω ω)
    (hRank : ∀ᵐ ω ∂μ, (A * Ω ω).rank = q) :
    Integrable (fun ω => frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω))) μ ∧
      (∫ ω, frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω)) ∂μ) ≤
        (1 + (q : ℝ) / (s - q - 1)) *
          ((1 + (k : ℝ) / (t - k - 1)) * frobSq S₂) := by
  let Q : Ωs → Matrix (Fin m) (Fin q) ℝ := fun ω => Qf (Matrix.of.symm (Ω ω))
  have hcompression := ae_isUnit_gaussian_compression_of_indep
    (fun ω => Matrix.of.symm (Ω ω)) (aemeasurable_of_map_eq_gaussianMatrix hΩ)
    (fun ω => Matrix.of.symm (Ψ ω)) hΨ hind Qf hQf hQo (by omega : q ≤ s)
  have hEq : (fun ω => frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω))) =ᵐ[μ]
      fun ω => frobSq (A - sketchedOutput (Q ω) (Ψ ω) A) := by
    filter_upwards [hQr, hRank, hcompression] with ω hproj hrank hinj
    rw [rawGeneralizedNystrom_eq_sketchedOutput A (A * Ω ω) (Q ω) (Ψ ω)
      hproj (by simpa only [Fintype.card_fin] using hrank) hinj]
  obtain ⟨hInt, hBound⟩ := integrable_and_integral_frobSq_sub_sketchedOutput_le_rank_factor_gaussian
    hA hU₂ hV₁ hV₂ hV hkt hqs hq Ω Ψ hΩ hΨ hind Q Qf hQf
    (fun _ => rfl) hQo hQr
  refine ⟨hInt.congr (hEq.mono fun _ h => h.symm), ?_⟩
  rw [integral_congr_ae hEq]
  exact hBound

/-- If an orthogonal-frame projector reproduces `A` and the second sketch is injective
on the frame, the normalized sketched output is exactly `A`.
Tropp–Webber 2023, §5; atlas `gn-expected-error` (exact recovery helper). -/
theorem sketchedOutput_eq_of_projector_eq
    {m n q s : Type*} [Fintype m] [Fintype n] [Fintype q] [Fintype s] [DecidableEq q]
    (A : Matrix m n ℝ) (Q : Matrix m q ℝ) (Ψ : Matrix m s ℝ)
    (hProj : Q * (Qᵀ * A) = A) (hΨ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) :
    sketchedOutput Q Ψ A = A := by
  calc
    sketchedOutput Q Ψ A = Q * pinvL (Ψᵀ * Q) * (Ψᵀ * A) := by
      simp only [sketchedOutput, sketchedCore, Matrix.mul_assoc]
    _ = Q * pinvL (Ψᵀ * Q) * (Ψᵀ * (Q * (Qᵀ * A))) := by rw [hProj]
    _ = Q * (pinvL (Ψᵀ * Q) * (Ψᵀ * Q)) * (Qᵀ * A) := by
      simp only [Matrix.mul_assoc]
    _ = A := by rw [pinvL_mul hΨ, Matrix.mul_one, hProj]

/-- **Raw Gaussian Nyström exact recovery in the rank-deficient sketch regime.**
If both Gaussian sketches have at least `rank A` columns, the actual raw Moore–Penrose
formula equals `A` almost surely. Independence between the sketches is unnecessary in
this exact recovery branch. Zero-rank inputs and empty dimensions are included.
Tropp–Webber 2023, §5; atlas `gn-expected-error`. -/
theorem ae_rawGeneralizedNystrom_eq_self_of_rank_le
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {m n t s : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ) (Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t)
    (hΨ : μ.map (fun ω => Matrix.of.symm (Ψ ω)) = gaussianMatrix m s)
    (hrt : A.rank ≤ t) (hrs : A.rank ≤ s) :
    ∀ᵐ ω ∂μ, rawGeneralizedNystrom A (A * Ω ω) (Ψ ω) = A := by
  obtain ⟨Q, hQo, hQA⟩ := exists_orthonormal_frame_reproducing_matrix A
  have hRank : ∀ᵐ ω ∂μ, (A * Ω ω).rank = A.rank := by
    simpa only [min_eq_left hrt, Equiv.apply_symm_apply] using
      ae_rank_mul_gaussian_eq_min A (fun ω => Matrix.of.symm (Ω ω)) hΩ
  have hUnit : ∀ᵐ ω ∂μ, IsUnit (((Ψ ω)ᵀ * Q)ᵀ * ((Ψ ω)ᵀ * Q)) := by
    have h := ae_isUnit_block hΨ Q hQo hrs
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Equiv.apply_symm_apply] using h
  filter_upwards [hRank, hUnit] with ω hrank hunit
  have hY : Q * (Qᵀ * (A * Ω ω)) = A * Ω ω := by
    calc
      Q * (Qᵀ * (A * Ω ω)) = (Q * (Qᵀ * A)) * Ω ω := by simp only [Matrix.mul_assoc]
      _ = A * Ω ω := by rw [hQA]
  exact (rawGeneralizedNystrom_eq_sketchedOutput A (A * Ω ω) Q (Ψ ω)
    hY (by simpa only [Fintype.card_fin] using hrank) hunit).trans
      (sketchedOutput_eq_of_projector_eq A Q (Ψ ω) hQA hunit)

/-- Actual raw Gaussian Nyström Frobenius bound in the full-column first-sketch regime.
The measurable polar frame and all its a.s. properties are constructed from `AΩ`;
no caller-supplied frame, rank or moment certificate remains.
Tropp–Webber 2023, Theorem 5.1; atlas `gn-expected-error`. -/
theorem integrable_and_integral_frobSq_rawGeneralizedNystrom_le_of_sketch_cols_le_rank
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {m n k r r' t s : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t) (htRank : t ≤ A.rank) (hst : t + 2 ≤ s)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ) (Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t)
    (hΨ : μ.map (fun ω => Matrix.of.symm (Ψ ω)) = gaussianMatrix m s)
    (hind : IndepFun (fun ω => Matrix.of.symm (Ω ω)) (fun ω => Matrix.of.symm (Ψ ω)) μ) :
    Integrable (fun ω => frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω))) μ ∧
      (∫ ω, frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω)) ∂μ) ≤
        (1 + (t : ℝ) / (s - t - 1)) *
          ((1 + (k : ℝ) / (t - k - 1)) * frobSq S₂) := by
  let Qf : (Fin n → Fin t → ℝ) → Matrix (Fin m) (Fin t) ℝ :=
    fun G => polarFrame (A * Matrix.of G)
  have hQf : ∀ i j, Measurable fun G => Qf G i j := by
    have hY : ∀ a b, Measurable fun G : Fin n → Fin t → ℝ => (A * Matrix.of G) a b :=
      measurable_mul_entry_of (fun _ _ => measurable_const)
        (fun _ _ => by simp only [Matrix.of_apply]; fun_prop)
    have hArray : Measurable fun G : Fin n → Fin t → ℝ => Matrix.of.symm (A * Matrix.of G) :=
      measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => hY a b
    intro i j
    exact (measurable_polarFrame_entry i j).comp hArray
  have hGood : ∀ᵐ ω ∂μ, IsUnit ((A * Ω ω)ᵀ * (A * Ω ω)) := by
    have h := gaussianMatrix_ae_isUnit_gram_mul_of_le_rank A htRank
    rw [← hΩ] at h
    exact ae_of_ae_map (aemeasurable_of_map_eq_gaussianMatrix hΩ) h
  have hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Qf (Matrix.of.symm (Ω ω))) := by
    filter_upwards [hGood] with ω hω
    exact hasOrthonormalCols_polarFrame (A * Ω ω) hω
  have hQr : ∀ᵐ ω ∂μ, Qf (Matrix.of.symm (Ω ω)) *
      ((Qf (Matrix.of.symm (Ω ω)))ᵀ * (A * Ω ω)) = A * Ω ω := by
    filter_upwards [hGood] with ω hω
    exact polarFrame_mul_transpose_mul_eq (A * Ω ω) hω
  have hRank : ∀ᵐ ω ∂μ, (A * Ω ω).rank = t := by
    simpa only [min_eq_right htRank, Equiv.apply_symm_apply] using
      ae_rank_mul_gaussian_eq_min A (fun ω => Matrix.of.symm (Ω ω)) hΩ
  exact integrable_and_integral_frobSq_rawGeneralizedNystrom_le_of_exact_rank_frame
    hA hU₂ hV₁ hV₂ hV hkt hst (by omega : 1 ≤ t) Ω Ψ hΩ hΨ hind Qf hQf hQo hQr hRank

/-- **The full raw Gaussian generalized Nyström bound.** For `Y=AΩ`, independent Gaussian
sketches and `q=min(rank A,t)`, the actual Moore–Penrose formula has integrable squared
error bounded by `(1+q/(s-q-1))(1+k/(t-k-1))‖S₂‖F²`. Only `t≥k+2` and `s≥q+2` are required.
No frame, range, rank, moment or completion certificate is assumed. Rank-deficient
first sketches and zero-rank inputs are included via exact recovery.
Tropp–Webber 2023, Theorem 5.1; atlas `gn-expected-error`. -/
theorem integrable_and_integral_frobSq_rawGeneralizedNystrom_le_rank_factor_gaussian
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {m n k r r' t s : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t) (hqs : min A.rank t + 2 ≤ s)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ) (Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t)
    (hΨ : μ.map (fun ω => Matrix.of.symm (Ψ ω)) = gaussianMatrix m s)
    (hind : IndepFun (fun ω => Matrix.of.symm (Ω ω)) (fun ω => Matrix.of.symm (Ψ ω)) μ) :
    Integrable (fun ω => frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω))) μ ∧
      (∫ ω, frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω)) ∂μ) ≤
        (1 + ((min A.rank t : ℕ) : ℝ) / (s - min A.rank t - 1)) *
          ((1 + (k : ℝ) / (t - k - 1)) * frobSq S₂) := by
  by_cases hrt : A.rank ≤ t
  · have hrs : A.rank ≤ s := by
      have hh : A.rank + 2 ≤ s := by simpa only [min_eq_left hrt] using hqs
      omega
    have hExact := ae_rawGeneralizedNystrom_eq_self_of_rank_le A Ω Ψ hΩ hΨ hrt hrs
    have hZero : (fun ω => frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω))) =ᵐ[μ]
        fun _ => (0 : ℝ) := hExact.mono fun ω hω => by
          change frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω)) = 0
          rw [hω]
          simp
    have hIntZero : Integrable (fun _ : Ωs => (0 : ℝ)) μ := integrable_const (0 : ℝ)
    refine ⟨hIntZero.congr (hZero.mono fun _ h => h.symm), ?_⟩
    rw [integral_congr_ae hZero, integral_zero]
    have htR : (k : ℝ) + 2 ≤ t := by exact_mod_cast hkt
    have hsR : ((min A.rank t : ℕ) : ℝ) + 2 ≤ s := by exact_mod_cast hqs
    have hden1 : (0 : ℝ) < (t : ℝ) - k - 1 := by linarith
    have hden2 : (0 : ℝ) < (s : ℝ) - min A.rank t - 1 := by linarith
    have hc1 : 0 ≤ 1 + (k : ℝ) / (t - k - 1) := by positivity
    have hc2 : 0 ≤ 1 + ((min A.rank t : ℕ) : ℝ) / (s - min A.rank t - 1) := by positivity
    exact mul_nonneg hc2 (mul_nonneg hc1 (frobSq_nonneg S₂))
  · have htRank : t ≤ A.rank := (not_le.mp hrt).le
    have hst : t + 2 ≤ s := by simpa only [min_eq_right htRank] using hqs
    simpa only [min_eq_right htRank] using
      integrable_and_integral_frobSq_rawGeneralizedNystrom_le_of_sketch_cols_le_rank
        hA hU₂ hV₁ hV₂ hV hkt htRank hst Ω Ψ hΩ hΨ hind

/-- **Full raw Gaussian generalized Nyström error relative to the actual optimum.**
For every fixed real matrix, all target ranks and independent Gaussian sketches,
the actual raw Moore–Penrose output has integrable squared Frobenius error at most
`(1+q/(s-q-1))(1+k/(t-k-1)) OPT²`, where `q=min(rank A,t)` and `OPT²` is the
infimum over every rank-at-most-`k` approximant. It requires only `t≥k+2` and `s≥q+2`;
no spectral decomposition, frame, rank, moment or completion certificate is supplied.
Tropp–Webber 2023, Theorem 5.1; atlas `gn-expected-error`. -/
theorem integrable_and_integral_frobSq_rawGeneralizedNystrom_le_bestRankFrobSq
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {m n k t s : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hkt : k + 2 ≤ t) (hqs : min A.rank t + 2 ≤ s)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ) (Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t)
    (hΨ : μ.map (fun ω => Matrix.of.symm (Ψ ω)) = gaussianMatrix m s)
    (hind : IndepFun (fun ω => Matrix.of.symm (Ω ω)) (fun ω => Matrix.of.symm (Ψ ω)) μ) :
    Integrable (fun ω => frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω))) μ ∧
      (∫ ω, frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω)) ∂μ) ≤
        (1 + ((min A.rank t : ℕ) : ℝ) / (s - min A.rank t - 1)) *
          ((1 + (k : ℝ) / (t - k - 1)) * bestRankFrobSq k A) := by
  by_cases hkn : k ≤ n
  · obtain ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, hOPT⟩ :=
      exists_svd_right_blocks A k hkn
    obtain ⟨hInt, hBound⟩ := integrable_and_integral_frobSq_rawGeneralizedNystrom_le_rank_factor_gaussian
      hA hU₂ hV₁ hV₂ hV hkt hqs Ω Ψ hΩ hΨ hind
    exact ⟨hInt, by simpa only [hOPT] using hBound⟩
  · have hrt : A.rank ≤ t := by
      have hRankWidth := A.rank_le_width
      omega
    have hrs : A.rank ≤ s := by
      have hh : A.rank + 2 ≤ s := by simpa only [min_eq_left hrt] using hqs
      omega
    have hExact := ae_rawGeneralizedNystrom_eq_self_of_rank_le A Ω Ψ hΩ hΨ hrt hrs
    have hZero : (fun ω => frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω))) =ᵐ[μ]
        fun _ => (0 : ℝ) := hExact.mono fun ω hω => by
          change frobSq (A - rawGeneralizedNystrom A (A * Ω ω) (Ψ ω)) = 0
          rw [hω]
          simp
    have hIntZero : Integrable (fun _ : Ωs => (0 : ℝ)) μ := integrable_const (0 : ℝ)
    refine ⟨hIntZero.congr (hZero.mono fun _ h => h.symm), ?_⟩
    rw [integral_congr_ae hZero, integral_zero]
    have htR : (k : ℝ) + 2 ≤ t := by exact_mod_cast hkt
    have hsR : ((min A.rank t : ℕ) : ℝ) + 2 ≤ s := by exact_mod_cast hqs
    have hden1 : (0 : ℝ) < (t : ℝ) - k - 1 := by linarith
    have hden2 : (0 : ℝ) < (s : ℝ) - min A.rank t - 1 := by linarith
    have hc1 : 0 ≤ 1 + (k : ℝ) / (t - k - 1) := by positivity
    have hc2 : 0 ≤ 1 + ((min A.rank t : ℕ) : ℝ) / (s - min A.rank t - 1) := by positivity
    have hOpt : 0 ≤ bestRankFrobSq k A := by
      rw [← frobSq_sub_truncatedSVD_eq_bestRankFrobSq A k]
      exact frobSq_nonneg _
    exact mul_nonneg hc2 (mul_nonneg hc1 hOpt)

end NLAlib
