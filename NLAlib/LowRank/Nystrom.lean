import Mathlib.LinearAlgebra.Matrix.PosDef
import NLAlib.Matrix.MoorePenrose
import NLAlib.Matrix.SpectralBounds
import NLAlib.Sketching.Leverage
import NLAlib.LowRank.OptimalError

/-!
# The Nyström approximation

For a square matrix `A` and a test matrix `Ω`, the Nyström approximation is
`A⟨Ω⟩ = AΩ (ΩᵀAΩ)⁺ ΩᵀA` (`NLAlib.nystrom`, with the Moore–Penrose inverse, so no rank condition
is needed).

## Structural identity (atlas `nystrom-structural`)

If `A = FᵀF` (every PSD matrix has such a factor, e.g. `F = A^{1/2}`), put `Y = FΩ` and
`P = Y Y⁺`, the orthogonal projector onto `range(FΩ)`. Then exactly

  `A − A⟨Ω⟩ = ((I − P)F)ᵀ ((I − P)F)`      (`sub_nystrom_eq_of_eq_transpose_mul`)

so `0 ⪯ A⟨Ω⟩ ⪯ A`, `tr(A − A⟨Ω⟩) = ‖(I − P)F‖_F²` and `‖A − A⟨Ω⟩‖ = ‖(I − P)F‖²` (an equality,
sharper than the `≤` of the atlas statement). No matrix square root is needed: any Gram factor
`F` works, and `A^{1/2}` is the special case `F = A^{1/2}`.

## Randomized bound (atlas `nystrom-randomized`)

With `Ω` an `n × t` standard Gaussian matrix and `t ≥ k + 2`,
`E tr(A − A⟨Ω⟩) ≤ (1 + k/(t−k−1)) · OPT_k(F)²` where `OPT_k(F)² = ‖F − ⟦F⟧ₖ‖_F²`
(`integrable_and_integral_trace_sub_nystrom_le`). For a PSD `A = FᵀF`,
`OPT_k(F)² = ∑_{i>k} λᵢ(A) = ‖A − ⟦A⟧ₖ‖_*`; that identification is not formalized here, so the
right-hand side is stated with `bestRankFrobSq k F`.

Sources: Gittens–Mahoney 2016, Lemma 1 and §3; Tropp–Webber 2023, §2 and Thm 5.1 (and the
references there); Martinsson–Tropp 2020, §14 (eq. (14.4)), §19.2.
Atlas: `nystrom-structural`, `nystrom-randomized`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

section Structural

variable {n t r : Type*} [Fintype n] [Fintype t] [Fintype r]

/-- The **Nyström approximation** `A⟨Ω⟩ = AΩ (ΩᵀAΩ)⁺ ΩᵀA`, with the Moore–Penrose inverse of
the core `ΩᵀAΩ`. Martinsson–Tropp 2020, eq. (14.4); Tropp–Webber 2023, §2.
Atlas `nystrom-structural`.
atlas: nystrom-structural -/
def nystrom (A : Matrix n n ℝ) (Ω : Matrix n t ℝ) : Matrix n n ℝ :=
  A * Ω * moorePenroseInverse (Ωᵀ * A * Ω) * (Ωᵀ * A)

/-- `A⟨Ω⟩ = Fᵀ P F` for a Gram factorisation `A = FᵀF`, where `P = (FΩ)(FΩ)⁺` is the orthogonal
projector onto `range(FΩ)`. Gittens–Mahoney 2016, Lemma 1 (with `F = A^{1/2}`).
Atlas `nystrom-structural`. -/
theorem nystrom_eq_of_eq_transpose_mul {F : Matrix r n ℝ} {A : Matrix n n ℝ}
    (hA : A = Fᵀ * F) (Ω : Matrix n t ℝ) :
    nystrom A Ω = Fᵀ * (F * Ω * moorePenroseInverse (F * Ω)) * F := by
  set Y := F * Ω with hY
  have h1 : A * Ω = Fᵀ * Y := by rw [hA, hY, Matrix.mul_assoc]
  have h2 : Ωᵀ * A * Ω = Yᵀ * Y := by
    rw [hA, hY, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have h3 : Ωᵀ * A = Yᵀ * F := by
    rw [hA, hY, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hP : (moorePenroseInverse Y)ᵀ * Yᵀ = Y * moorePenroseInverse Y := by
    rw [← Matrix.transpose_mul]; exact (mul_moorePenroseInverse_isSymm Y).eq
  have hPP : Y * moorePenroseInverse Y * (Y * moorePenroseInverse Y) =
      Y * moorePenroseInverse Y := mul_moorePenroseInverse_isIdempotentElem Y
  unfold nystrom
  rw [h1, h2, h3, moorePenroseInverse_transpose_mul_self]
  calc Fᵀ * Y * (moorePenroseInverse Y * (moorePenroseInverse Y)ᵀ) * (Yᵀ * F)
      = Fᵀ * (Y * moorePenroseInverse Y * ((moorePenroseInverse Y)ᵀ * Yᵀ)) * F := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP, hPP]

/-- **Nyström structural identity** (exact form): if `A = FᵀF` then
`A − A⟨Ω⟩ = ((I − P)F)ᵀ((I − P)F)` with `P = (FΩ)(FΩ)⁺`. Gittens–Mahoney 2016, Lemma 1;
Tropp–Webber 2023, §2. Atlas `nystrom-structural`. Deviation: stated for any Gram factor `F`
(the source uses `F = A^{1/2}`); it is an identity, not only the bound of the source.
atlas: nystrom-structural -/
theorem sub_nystrom_eq_of_eq_transpose_mul [DecidableEq r] {F : Matrix r n ℝ}
    {A : Matrix n n ℝ} (hA : A = Fᵀ * F) (Ω : Matrix n t ℝ) :
    A - nystrom A Ω =
      ((1 - F * Ω * moorePenroseInverse (F * Ω)) * F)ᵀ *
        ((1 - F * Ω * moorePenroseInverse (F * Ω)) * F) := by
  set P := F * Ω * moorePenroseInverse (F * Ω) with hPdef
  have hPs : Pᵀ = P := (mul_moorePenroseInverse_isSymm (F * Ω)).eq
  have hPi : P * P = P := mul_moorePenroseInverse_isIdempotentElem (F * Ω)
  have hQ : (1 - P)ᵀ * (1 - P) = 1 - P := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hPs, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hPi]
    abel
  rw [nystrom_eq_of_eq_transpose_mul hA Ω, Matrix.transpose_mul]
  calc A - Fᵀ * P * F = Fᵀ * (1 - P) * F := by
        rw [hA, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    _ = Fᵀ * ((1 - P)ᵀ * (1 - P)) * F := by rw [hQ]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- `A − A⟨Ω⟩` is positive semidefinite when `A = FᵀF`, i.e. `A⟨Ω⟩ ⪯ A`.
Gittens–Mahoney 2016, Lemma 1; Martinsson–Tropp 2020, §14. Atlas `nystrom-structural`. -/
theorem posSemidef_sub_nystrom_of_eq_transpose_mul [DecidableEq r] {F : Matrix r n ℝ}
    {A : Matrix n n ℝ} (hA : A = Fᵀ * F) (Ω : Matrix n t ℝ) :
    (A - nystrom A Ω).PosSemidef := by
  rw [sub_nystrom_eq_of_eq_transpose_mul hA Ω, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `A⟨Ω⟩` is positive semidefinite when `A = FᵀF`, i.e. `0 ⪯ A⟨Ω⟩`.
Gittens–Mahoney 2016, Lemma 1; Martinsson–Tropp 2020, §14. Atlas `nystrom-structural`. -/
theorem posSemidef_nystrom_of_eq_transpose_mul {F : Matrix r n ℝ} {A : Matrix n n ℝ}
    (hA : A = Fᵀ * F) (Ω : Matrix n t ℝ) : (nystrom A Ω).PosSemidef := by
  set P := F * Ω * moorePenroseInverse (F * Ω)
  have hPs : Pᵀ = P := (mul_moorePenroseInverse_isSymm (F * Ω)).eq
  have hPi : P * P = P := mul_moorePenroseInverse_isIdempotentElem (F * Ω)
  have h : nystrom A Ω = (P * F)ᵀ * (P * F) := by
    rw [nystrom_eq_of_eq_transpose_mul hA Ω, Matrix.transpose_mul, hPs]
    calc Fᵀ * P * F = Fᵀ * (P * P) * F := by rw [hPi]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `tr(A − A⟨Ω⟩) = ‖(I − P)F‖_F²` for `A = FᵀF`, `P = (FΩ)(FΩ)⁺`. Gittens–Mahoney 2016,
Lemma 1; Tropp–Webber 2023, §2. Atlas `nystrom-structural`.
atlas: nystrom-structural -/
theorem trace_sub_nystrom_eq_of_eq_transpose_mul [DecidableEq r] {F : Matrix r n ℝ}
    {A : Matrix n n ℝ} (hA : A = Fᵀ * F) (Ω : Matrix n t ℝ) :
    (A - nystrom A Ω).trace = frobSq ((1 - F * Ω * moorePenroseInverse (F * Ω)) * F) := by
  rw [sub_nystrom_eq_of_eq_transpose_mul hA Ω, frobSq, frobInner_eq_trace]

/-- `‖A − A⟨Ω⟩‖₂ = ‖(I − P)F‖₂²` for `A = FᵀF`, `P = (FΩ)(FΩ)⁺`. Gittens–Mahoney 2016, Lemma 1
(stated there as `≤` with `F = A^{1/2}`). Atlas `nystrom-structural`. Deviation: equality.
atlas: nystrom-structural -/
theorem specNorm_sub_nystrom_eq_of_eq_transpose_mul [DecidableEq n] [DecidableEq r]
    {F : Matrix r n ℝ} {A : Matrix n n ℝ} (hA : A = Fᵀ * F) (Ω : Matrix n t ℝ) :
    specNorm (A - nystrom A Ω) =
      specNorm ((1 - F * Ω * moorePenroseInverse (F * Ω)) * F) ^ 2 := by
  rw [sub_nystrom_eq_of_eq_transpose_mul hA Ω, specNorm_sq_eq_specNorm_transpose_mul_self]

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- A real positive semidefinite matrix is a Gram matrix: `A = FᵀF` for some square `F`.
Mathlib `CStarAlgebra.nonneg_iff_eq_star_mul_self`. Atlas `nystrom-structural` (helper). -/
theorem exists_eq_transpose_mul_of_posSemidef [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : ∃ F : Matrix n n ℝ, A = Fᵀ * F := by
  obtain ⟨F, hF⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨F, by rw [hF, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]⟩

/-- **Nyström, lower Loewner bound**: for `A` positive semidefinite and any `Ω`, `0 ⪯ A⟨Ω⟩`.
Gittens–Mahoney 2016, Lemma 1; Martinsson–Tropp 2020, §14. Atlas `nystrom-structural`.
atlas: nystrom-structural -/
theorem posSemidef_nystrom [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (Ω : Matrix n t ℝ) : (nystrom A Ω).PosSemidef := by
  obtain ⟨F, hF⟩ := exists_eq_transpose_mul_of_posSemidef hA
  exact posSemidef_nystrom_of_eq_transpose_mul hF Ω

/-- **Nyström, upper Loewner bound**: for `A` positive semidefinite and any `Ω`, `A⟨Ω⟩ ⪯ A`,
i.e. `A − A⟨Ω⟩` is positive semidefinite. Gittens–Mahoney 2016, Lemma 1; Martinsson–Tropp
2020, §14. Atlas `nystrom-structural`.
atlas: nystrom-structural -/
theorem posSemidef_sub_nystrom [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (Ω : Matrix n t ℝ) : (A - nystrom A Ω).PosSemidef := by
  obtain ⟨F, hF⟩ := exists_eq_transpose_mul_of_posSemidef hA
  exact posSemidef_sub_nystrom_of_eq_transpose_mul hF Ω

/-- `(I − Y Y⁺)F` is the residual of `F` with respect to any orthonormal frame `Q` of
`range Y`: if `QᵀQ = I`, `range Y ⊆ range Q` and `Q` has at most `rank Y` columns, then
`(I − YY⁺)F = (I − QQᵀ)F`. Atlas `nystrom-randomized` (helper; uses `leverage-scores`'
projector uniqueness). -/
theorem one_sub_mul_moorePenroseInverse_mul_eq_residual {m q p : Type*} [Fintype m]
    [Fintype q] [DecidableEq m] [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    {Y : Matrix m t ℝ} (hQY : Q * (Qᵀ * Y) = Y) (hr : Fintype.card q ≤ Y.rank)
    (F : Matrix m p ℝ) : (1 - Y * moorePenroseInverse Y) * F = residual Q F := by
  rw [← mul_transpose_eq_mul_moorePenroseInverse hQ hQY hr, residual_eq_one_sub_mul]

end Structural

section Randomized

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]

/-- **Randomized Nyström, expected trace error** (Gittens–Mahoney 2016, Thm 3 / §3;
Tropp–Webber 2023, Thm 5.1 specialised to Nyström; Martinsson–Tropp 2020, §19.2): if
`A = FᵀF` and `Ω` is an `n × t` standard Gaussian matrix with `t ≥ k + 2`, then
`tr(A − A⟨Ω⟩)` is integrable and
`E tr(A − A⟨Ω⟩) ≤ (1 + k/(t−k−1)) · ‖F − ⟦F⟧ₖ‖_F²`.

Proof: `tr(A − A⟨Ω⟩) = ‖(I − P)F‖_F²` (`trace_sub_nystrom_eq_of_eq_transpose_mul`); a.s.
the Gaussian range frame `Q` of `FΩ` has `min(rank F, t) = rank(FΩ)` columns, so `QQᵀ = P`;
then the Gaussian RSVD bound for `F`
(`integrable_and_integral_frobSq_residual_gaussianRangeFrame_le_bestRankFrobSq`).

Deviation: the right side is `bestRankFrobSq k F`; for `A = FᵀF` this equals
`∑_{i>k} λᵢ(A) = ‖A − ⟦A⟧ₖ‖_*` (the atlas form), an identification not formalized here.
Index types are `Fin` (Gaussian law convention). Atlas `nystrom-randomized` (uses
`nystrom-structural`, `rsvd-expected-error`, `leverage-scores`).
atlas: nystrom-randomized (partial) -/
theorem integrable_and_integral_trace_sub_nystrom_le {n r k t : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {F : Matrix (Fin r) (Fin n) ℝ} (hA : A = Fᵀ * F)
    (hkt : k + 2 ≤ t) (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t) :
    Integrable (fun ω => (A - nystrom A (Ω ω)).trace) μ ∧
      ∫ ω, (A - nystrom A (Ω ω)).trace ∂μ ≤ (1 + (k : ℝ) / (t - k - 1)) * bestRankFrobSq k F := by
  obtain ⟨hint, hle⟩ :=
    integrable_and_integral_frobSq_residual_gaussianRangeFrame_le_bestRankFrobSq F hkt Ω hΩ
  have hae : (fun ω => frobSq (residual (gaussianRangeFrame F t (Matrix.of.symm (Ω ω))) F))
      =ᵐ[μ] fun ω => (A - nystrom A (Ω ω)).trace := by
    have ho := ae_hasOrthonormalCols_gaussianRangeFrame_of_map_eq F
      (fun ω => Matrix.of.symm (Ω ω)) hΩ
    have hp := ae_project_gaussianRangeFrame_of_map_eq F (fun ω => Matrix.of.symm (Ω ω)) hΩ
    have hrk := ae_rank_mul_gaussian_eq_min F (fun ω => Matrix.of.symm (Ω ω)) hΩ
    filter_upwards [ho, hp, hrk] with ω hω hpω hrω
    simp only [Equiv.apply_symm_apply] at hpω hrω
    rw [trace_sub_nystrom_eq_of_eq_transpose_mul hA,
      one_sub_mul_moorePenroseInverse_mul_eq_residual hω hpω (by rw [hrω, Fintype.card_fin]) F]
  exact ⟨hint.congr hae, (integral_congr_ae hae).symm.le.trans hle⟩

end Randomized

end NLAlib
