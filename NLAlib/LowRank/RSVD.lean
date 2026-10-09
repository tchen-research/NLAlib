import NLAlib.LowRank.RangeFinder
import NLAlib.LowRank.Assembly

/-!
# Expected error of the randomized SVD (Frobenius norm)

Chen–Persson, *One- and two-pass algorithms for low-rank approximation*, Theorem `thm:RSVD`
(the Frobenius-norm expected error bound of HMT 2011, Thm 10.5):

  `E‖A − QQᵀA‖_F² ≤ (1 + k/(t−k−1)) ‖A − ⟦A⟧ₖ‖_F²`,

and the same bound for the truncated output `Q⟦QᵀA⟧ₖ`. This file assembles the deterministic
range-finder bound of `NLAlib/LowRank/RangeFinder.lean` (HMT 2011, Thm 9.1, Frobenius form;
Chen–Persson `prop:hmt-struct`) with the expectation-level arithmetic of
`NLAlib/LowRank/Assembly.lean`.

Ported from the LRA project (Chen–Persson formalization, same Mathlib pin),
`LRA/Theorems/RSVDandGN.lean`. The deterministic helpers of that file are already in NLAlib:
LRA `frobSq_residual_le` is `NLAlib.frobSq_residual_le_frobSq_sub_mul`
(`NLAlib/Matrix/Projections.lean`), and LRA `hmt_second_frob` / `hmt_second_residual` are
`NLAlib.rangeFinder_frobSq_le` (whose conclusion `frobSq (residual Q A)` is by definition
`frobSq (A − Q(QᵀA))`); LRA `hmt_third` is `NLAlib.rangeFinder_truncated_frobSq_le`.

## Model

* Probability space `{Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs}
  [IsProbabilityMeasure μ]`; expectations are Bochner integrals `∫ ω, · ∂μ`.
* Random test matrix `Ω : Ωs → Matrix (Fin n) (Fin t) ℝ`.
* `A` is fixed with the block SVD of `RangeFinder.lean`: `A = U₁ S₁ V₁ᵀ + U₂ S₂ V₂ᵀ`, so that
  the paper's `OPT² = ‖A − ⟦A⟧ₖ‖_F² = ‖Σ₂‖_F²` is `frobSq S₂`.
* `Q ω = orth(A Ω ω)` enters only through `HasOrthonormalCols (Q ω)` and
  `range(AΩ) ⊆ range(Q)` (`Q ω * (Q ωᵀ * (A * Ω ω)) = A * Ω ω`), both almost surely.
  The paper's `q = rank(AΩ)` is a *random* number of columns; since the column index type
  `Fin q` is fixed at the type level, `q` is a fixed natural number (generic case `q = t`).
* `⟦C⟧ₖ` is any `Y` with `IsBestRankApprox k C Y` (Eckart–Young is not used).

## Trust boundary

Every Gaussian fact enters as an explicit hypothesis on an expectation, in exactly the form the
paper uses it after conditioning (`hinv`); "almost surely full rank" enters as
`∀ᵐ ω ∂μ, IsUnit (…)`; integrability is explicit. Everything else is proved.

## Deviation from the LRA source

The row index types are `Fin m`, `Fin n` (the LRA source allows arbitrary `Fintype` types),
because `NLAlib.rangeFinder_frobSq_le` is stated over `Fin`; this is also the convention for
statements involving a Gaussian law (CONTRIBUTING §3). The proofs do not use `Fin` and would
generalise verbatim once `RangeFinder.lean` does.

Atlas: `rsvd-expected-error`.
-/

noncomputable section
set_option autoImplicit false
-- `k + 2 ≤ t` is needed only to make the Gaussian hypothesis `hinv` true; it is kept in the
-- statements for fidelity, hence this option.
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Almost-everywhere variant of the RSVD assembly -/

section Assembly

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs}

/-- `Assembly.rsvd_assembly` with the pointwise structural bound required only almost surely
(the range finder's hypotheses `QᵀQ = I`, `range(AΩ) ⊆ range(Q)` and "`Ω₁` has full row rank"
hold only almost surely). Chen–Persson, proof of `thm:RSVD`. Atlas `rsvd-expected-error`. -/
theorem rsvd_assembly_ae [IsProbabilityMeasure μ] {X Zsq : Ωs → ℝ} {OPTsq c : ℝ}
    (hX : ∀ᵐ ω ∂μ, X ω ≤ OPTsq + Zsq ω) (hZ : ∫ ω, Zsq ω ∂μ = c * OPTsq)
    (hXi : Integrable X μ) (hZi : Integrable Zsq μ) :
    ∫ ω, X ω ∂μ ≤ (1 + c) * OPTsq := by
  calc ∫ ω, X ω ∂μ ≤ ∫ ω, (OPTsq + Zsq ω) ∂μ :=
        integral_mono_ae hXi ((integrable_const _).add hZi) hX
    _ = OPTsq + c * OPTsq := by
        rw [integral_add (integrable_const _) hZi, integral_const, probReal_univ, one_smul, hZ]
    _ = (1 + c) * OPTsq := by ring

end Assembly

/-! ### Main theorems -/

section Main

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs}
variable {m n k r r' t q : ℕ}

/-- **Randomized SVD, truncated output** (Chen–Persson, Theorem `thm:RSVD` for Algorithm
tRSVD, output `Q ⟦QᵀA⟧ₖ`; HMT 2011, Thm 10.5, Frobenius case).

Setting: `A = U₁S₁V₁ᵀ + U₂S₂V₂ᵀ` (block SVD, `OPT² = frobSq S₂`), random `Ω`, `t ≥ k + 2`.
* `Q ω = orth(AΩ ω)`: a.s. orthonormal columns (`hQo`) and `range(AΩ) ⊆ range(Q)` (`hQr`);
* `Y ω = ⟦Q ωᵀ A⟧ₖ`: any best rank-`k` approximation (`hY`);
* `hunit`: `Ω₁ = V₁ᵀΩ` has full row rank a.s. (`prop:hmt-struct`, rotational invariance);
* `hinv`: `E‖Σ₂Ω₂Ω₁†‖_F² = (k/(t−k−1)) ‖Σ₂‖_F²` — `lem:moments` + `lem:invmom` + tower
  property, exactly the display in the proof of `thm:RSVD` (needs `t ≥ k+2`);
* `hXi`, `hZi`: integrability.
Conclusion: `E‖A − Q⟦QᵀA⟧ₖ‖_F² ≤ (1 + k/(t−k−1)) ‖A − ⟦A⟧ₖ‖_F²`.
Deviation: row index types `Fin m`, `Fin n` (see the module docstring).
Atlas `rsvd-expected-error`. -/
theorem rsvd_truncated_main [IsProbabilityMeasure μ]
    {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ) (Q : Ωs → Matrix (Fin m) (Fin q) ℝ)
    (Y : Ωs → Matrix (Fin q) (Fin n) ℝ)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω)
    (hY : ∀ ω, IsBestRankApprox k ((Q ω)ᵀ * A) (Y ω))
    (hunit : ∀ᵐ ω ∂μ, IsUnit ((V₁ᵀ * Ω ω) * (V₁ᵀ * Ω ω)ᵀ))
    (hinv : ∫ ω, frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ∂μ
      = (k : ℝ) / (t - k - 1) * frobSq S₂)
    (hXi : Integrable (fun ω => frobSq (A - Q ω * Y ω)) μ)
    (hZi : Integrable (fun ω => frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) μ) :
    ∫ ω, frobSq (A - Q ω * Y ω) ∂μ ≤ (1 + (k : ℝ) / (t - k - 1)) * frobSq S₂ := by
  have hX : ∀ᵐ ω ∂μ, frobSq (A - Q ω * Y ω)
      ≤ frobSq S₂ + frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) := by
    filter_upwards [hQo, hQr, hunit] with ω h1 h2 h3
    exact rangeFinder_truncated_frobSq_le hA hU₂ hV₁ hV₂ hV rfl rfl h3 h1 h2 (hY ω)
  exact rsvd_assembly_ae hX hinv hXi hZi

/-- **Randomized SVD** (Chen–Persson, Theorem `thm:RSVD` for Algorithm RSVD, untruncated output
`Q QᵀA`; HMT 2011, Thm 10.5, Frobenius case).

Same hypotheses as `rsvd_truncated_main` except that no truncation `Y` is needed: the proof
goes through the second inequality of `prop:hmt-struct` (`rangeFinder_frobSq_le`, i.e.
`‖A − QQᵀA‖_F ≤ ‖A − QB‖_F` for every `B`, applied to `B = QᵀZ`), the untruncated analogue
of the argument for `Q⟦QᵀA⟧ₖ`. (Equivalently, `frobSq (A − Q(QᵀA)) ≤ frobSq (A − QY)` for
the truncated output, see `frobSq_rsvd_le_trsvd`.)
Conclusion: `E‖A − QQᵀA‖_F² ≤ (1 + k/(t−k−1)) ‖A − ⟦A⟧ₖ‖_F²`.
Deviation: row index types `Fin m`, `Fin n` (see the module docstring).
Atlas `rsvd-expected-error`. -/
theorem rsvd_main [IsProbabilityMeasure μ]
    {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ) (Q : Ωs → Matrix (Fin m) (Fin q) ℝ)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω)
    (hunit : ∀ᵐ ω ∂μ, IsUnit ((V₁ᵀ * Ω ω) * (V₁ᵀ * Ω ω)ᵀ))
    (hinv : ∫ ω, frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ∂μ
      = (k : ℝ) / (t - k - 1) * frobSq S₂)
    (hXi : Integrable (fun ω => frobSq (A - Q ω * ((Q ω)ᵀ * A))) μ)
    (hZi : Integrable (fun ω => frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) μ) :
    ∫ ω, frobSq (A - Q ω * ((Q ω)ᵀ * A)) ∂μ ≤ (1 + (k : ℝ) / (t - k - 1)) * frobSq S₂ := by
  have hX : ∀ᵐ ω ∂μ, frobSq (A - Q ω * ((Q ω)ᵀ * A))
      ≤ frobSq S₂ + frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) := by
    filter_upwards [hQo, hQr, hunit] with ω h1 h2 h3
    exact rangeFinder_frobSq_le hA hU₂ hV₁ hV₂ hV rfl rfl h3 h1 h2
  exact rsvd_assembly_ae hX hinv hXi hZi

end Main

/-- Untruncated-vs-truncated comparison (Chen–Persson, remark after `thm:RSVD` / proof of
`rsvd_main`): the RSVD output error is bounded by the tRSVD output error, pointwise, for any
`Y` (in particular `Y = ⟦QᵀA⟧ₖ`). A restatement of
`NLAlib.frobSq_residual_le_frobSq_sub_mul` (LRA `frobSq_residual_le`) with the residual
written out. Atlas `rsvd-expected-error`. -/
theorem frobSq_rsvd_le_trsvd {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    [DecidableEq q] (A : Matrix m n ℝ) (Q : Matrix m q ℝ)
    (hQo : HasOrthonormalCols Q) (Y : Matrix q n ℝ) :
    frobSq (A - Q * (Qᵀ * A)) ≤ frobSq (A - Q * Y) :=
  frobSq_residual_le_frobSq_sub_mul hQo A Y

end NLAlib

end
