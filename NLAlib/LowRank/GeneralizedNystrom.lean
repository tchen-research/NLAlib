import NLAlib.LowRank.RSVD
import NLAlib.LowRank.SketchedRegression

/-!
# Expected error of the generalized Nyström method (Frobenius norm)

Chen–Persson, *One- and two-pass algorithms for low-rank approximation*:

* `completion_reduction` — Lemma `lem:completion`, reduced to its two Gaussian moment inputs:
  `E‖A − Q(ΨᵀQ)†ΨᵀA‖_F² = (1 + q/(s−q−1)) ‖(I − QQᵀ)A‖_F²`;
* `gn_main` (and `gn_main_of_completion`) — Theorem `thm:GN` (Tropp–Webber 2023, Thm 5.1):
  `E‖A − Â‖_F² ≤ (1 + t/(s−t−1)) (1 + k/(t−k−1)) ‖A − ⟦A⟧ₖ‖_F²`.

This file assembles the deterministic identities of `NLAlib/LowRank/SketchedRegression.lean`,
the range-finder bound of `NLAlib/LowRank/RangeFinder.lean` (HMT 2011, Thm 9.1) and the
expectation-level arithmetic of `NLAlib/LowRank/Assembly.lean` and `NLAlib/LowRank/RSVD.lean`.

Ported from the LRA project (Chen–Persson formalization, same Mathlib pin),
`LRA/Theorems/RSVDandGN.lean`.

## Model

As in `NLAlib/LowRank/RSVD.lean`, plus a second random sketch `Ψ : Ωs → Matrix m (Fin s) ℝ`.
`Â ω = sketchedOutput (Q ω) (Ψ ω) A = Q(ΨᵀQ)†ΨᵀA`. The paper's `q = rank(AΩ)` is a fixed
natural number with the deterministic bound `q ≤ t` as a hypothesis (generic case `q = t`).

## Trust boundary

Every Gaussian fact enters as an explicit hypothesis on an expectation, in exactly the form the
paper uses it after conditioning (`hinv`, `hG₂`, `hG₁m`, `hcond`, `hG`); "almost surely full
rank" facts enter as `∀ᵐ ω ∂μ, IsUnit (…)`; integrability is explicit. Everything else is proved.

## Index types

As in the LRA source, the row and block index types `m`, `n`, `r`, `r'` (and the completion's
column type) are arbitrary `Fintype`s; `k`, `t`, `s`, `q` are natural numbers because they
appear in the constants.

Atlas: `gn-expected-error`.
-/

noncomputable section
set_option autoImplicit false
-- Some size hypotheses (`k + 2 ≤ t`, `1 ≤ q`, `q + 2 ≤ s`) are needed only to make the Gaussian
-- hypotheses true; they are kept in the statements for fidelity, hence this option.
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs}

/-- **Exact Gaussian completion, deterministic reduction** (Chen–Persson, Lemma
`lem:completion`; Tropp–Webber 2023, proof of Thm 5.1).

Fixed `Q` (orthonormal columns, `q ≥ 1`), its orthogonal completion `Qp = Q⊥`
(`QQᵀ + Q⊥Q⊥ᵀ = I`), fixed `A`, random `Ψ` with `s ≥ q + 2`; `G₁ ω = Ψ ωᵀ Q`,
`G₂ ω = Ψ ωᵀ Q⊥`, `E = residual Q A = (I − QQᵀ)A`.
* `hG₁`: `G₁` has full column rank a.s. (so `G₁†G₁ = I`), the "almost surely" of the paper;
* `hG₂`: `E‖G₁†G₂(Q⊥ᵀE)‖_F² = E‖G₁†‖_F² · ‖Q⊥ᵀE‖_F²` — `lem:moments` for `G₂` conditionally
  on `G₁` (independence of `G₁`, `G₂`) followed by the tower property;
* `hG₁m`: `E‖G₁†‖_F² = q/(s−q−1)` — `lem:invmom` (needs `s ≥ q+2`, `q ≥ 1`);
* `hGi`: integrability of the noise term.
Everything else in the paper's proof (`ΨᵀA = G₁QᵀA + G₂Q⊥ᵀE`, `X̂ = QᵀA + G₁†G₂Q⊥ᵀE`,
Pythagoras, `‖Q⊥ᵀE‖_F = ‖E‖_F`) is proved in `SketchedRegression.lean` and used here.
Conclusion: `eq:completion`,
`E‖A − Q(ΨᵀQ)†ΨᵀA‖_F² = (1 + q/(s−q−1)) ‖(I − QQᵀ)A‖_F²`.
Atlas `gn-expected-error` (helper; uses `sketched-regression`, `orthonormal-completion`). -/
theorem completion_reduction {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq m] [DecidableEq r] {q s : ℕ} [IsProbabilityMeasure μ]
    (Q : Matrix m (Fin q) ℝ) (Qp : Matrix m r ℝ) (A : Matrix m n ℝ)
    (hQ : HasOrthonormalCols Q) (hQp : HasOrthonormalCols Qp) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1)
    (hq : 1 ≤ q) (hqs : q + 2 ≤ s)
    (Ψ : Ωs → Matrix m (Fin s) ℝ)
    (hG₁ : ∀ᵐ ω ∂μ, IsUnit (((Ψ ω)ᵀ * Q)ᵀ * ((Ψ ω)ᵀ * Q)))
    (hG₂ : ∫ ω, frobSq (pinvL ((Ψ ω)ᵀ * Q) * ((Ψ ω)ᵀ * Qp) * (Qpᵀ * residual Q A)) ∂μ
      = (∫ ω, frobSq (pinvL ((Ψ ω)ᵀ * Q)) ∂μ) * frobSq (Qpᵀ * residual Q A))
    (hG₁m : ∫ ω, frobSq (pinvL ((Ψ ω)ᵀ * Q)) ∂μ = (q : ℝ) / (s - q - 1))
    (hGi : Integrable
      (fun ω => frobSq (pinvL ((Ψ ω)ᵀ * Q) * ((Ψ ω)ᵀ * Qp) * (Qpᵀ * residual Q A))) μ) :
    ∫ ω, frobSq (A - sketchedOutput Q (Ψ ω) A) ∂μ
      = (1 + (q : ℝ) / (s - q - 1)) * frobSq (residual Q A) := by
  have hae : (fun ω => frobSq (A - sketchedOutput Q (Ψ ω) A)) =ᵐ[μ]
      fun ω => frobSq (residual Q A)
        + frobSq (pinvL ((Ψ ω)ᵀ * Q) * ((Ψ ω)ᵀ * Qp) * (Qpᵀ * residual Q A)) := by
    filter_upwards [hG₁] with ω h
    exact frobSq_error Q Qp (Ψ ω) A hQ hcomp h
  rw [integral_congr_ae hae, integral_add (integrable_const _) hGi, integral_const,
    probReal_univ, one_smul, hG₂, hG₁m, frobSq_transpose_mul_residual Q Qp A hQ hQp hcomp]
  ring

section Main

variable {m n r r' : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype r'] [DecidableEq r]
  [DecidableEq r'] {k t s q : ℕ}

/-- **Generalized Nyström expected error** (Chen–Persson, Theorem `thm:GN`; Tropp–Webber 2023,
Thm 5.1). Output `Â ω = sketchedOutput (Q ω) (Ψ ω) A = Q(ΨᵀQ)†ΨᵀA` with `Q ω = orth(AΩ ω)`
having `q` columns, `q ≤ t` (the paper's `q = rank(AΩ)`; here `q` is fixed, the generic case
being `q = t`), `t ≥ k+2`, `s ≥ t+2`.
* `hQo`, `hQr`, `hunit`, `hinv`: as in `rsvd_truncated_main` (`prop:hmt-struct` inputs and
  the Gaussian moment identity of the proof of `thm:RSVD`);
* `hcond`: `lem:completion` applied conditionally on `Ω` (independence of `Ψ` and `Ω`), then
  the tower property: `E‖A − Â‖_F² = E[(1 + q/(s−q−1)) ‖(I − QQᵀ)A‖_F²]`. Its per-`Ω` content
  is `completion_reduction`; see `gn_main_of_completion` for a version whose hypothesis is the
  Gaussian noise moment instead;
* `hYi`, `hZi`: integrability of `‖(I − QQᵀ)A‖_F²` and `‖Σ₂Ω₂Ω₁†‖_F²`.
Conclusion: `E‖A − Â‖_F² ≤ (1 + t/(s−t−1)) (1 + k/(t−k−1)) ‖A − ⟦A⟧ₖ‖_F²`.
Atlas `gn-expected-error` (uses `rsvd-expected-error`, `hmt-9-1-frobenius`). -/
theorem gn_main [IsProbabilityMeasure μ]
    {A : Matrix m n ℝ} {U₁ : Matrix m (Fin k) ℝ} {U₂ : Matrix m r ℝ}
    {V₁ : Matrix n (Fin k) ℝ} {V₂ : Matrix n r' ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t) (hts : t + 2 ≤ s) (hqt : q ≤ t)
    (Ω : Ωs → Matrix n (Fin t) ℝ) (Ψ : Ωs → Matrix m (Fin s) ℝ)
    (Q : Ωs → Matrix m (Fin q) ℝ)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω)
    (hunit : ∀ᵐ ω ∂μ, IsUnit ((V₁ᵀ * Ω ω) * (V₁ᵀ * Ω ω)ᵀ))
    (hinv : ∫ ω, frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ∂μ
      = (k : ℝ) / (t - k - 1) * frobSq S₂)
    (hcond : ∫ ω, frobSq (A - sketchedOutput (Q ω) (Ψ ω) A) ∂μ
      = ∫ ω, (1 + (q : ℝ) / (s - q - 1)) * frobSq (residual (Q ω) A) ∂μ)
    (hYi : Integrable (fun ω => frobSq (residual (Q ω) A)) μ)
    (hZi : Integrable (fun ω => frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) μ) :
    ∫ ω, frobSq (A - sketchedOutput (Q ω) (Ψ ω) A) ∂μ
      ≤ (1 + (t : ℝ) / (s - t - 1)) * ((1 + (k : ℝ) / (t - k - 1)) * frobSq S₂) := by
  -- the range-finder bound, `thm:RSVD` for `Y = ‖(I - QQᵀ)A‖_F²`
  have hstruct : ∀ᵐ ω ∂μ, frobSq (residual (Q ω) A)
      ≤ frobSq S₂ + frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) := by
    filter_upwards [hQo, hQr, hunit] with ω h1 h2 h3
    exact frobSq_residual_le_of_range_subset hA hU₂ hV₁ hV₂ hV rfl rfl h3 h1 h2
  have hYbound := rsvd_assembly_ae hstruct hinv hYi hZi
  -- the completion factor: `q/(s-q-1) ≤ t/(s-t-1)` since `q ≤ t < s - 1`
  have hts' : (t : ℝ) < s - 1 := by
    have : (t : ℝ) + 2 ≤ s := by exact_mod_cast hts
    linarith
  have hfac : (q : ℝ) / (s - q - 1) ≤ (t : ℝ) / (s - t - 1) :=
    Assembly.completion_factor_mono (Nat.cast_nonneg q) (by exact_mod_cast hqt) hts'
  have hcmax : 0 ≤ 1 + (t : ℝ) / (s - t - 1) := by
    have : 0 ≤ (t : ℝ) / (s - t - 1) := div_nonneg (Nat.cast_nonneg t) (by linarith)
    linarith
  exact Assembly.gn_assembly (cfac := fun _ => 1 + (q : ℝ) / (s - q - 1))
    (fun ω => frobSq_nonneg _) hcmax (fun _ => by linarith) hcond hYbound
    (hYi.const_mul _) hYi

/-- **Generalized Nyström expected error** (Chen–Persson, Theorem `thm:GN`; Tropp–Webber 2023,
Thm 5.1), variant of `gn_main` in which the conditional completion identity `hcond` is
*derived* from `frobSq_error` (`SketchedRegression.lean`) and the Gaussian noise-moment
identity after conditioning on `Ω` and the tower property:
* `Qp ω = Q ω⊥` is an orthogonal completion of `Q ω` (a.s. `QQᵀ + Q⊥Q⊥ᵀ = I`);
* `hG₁`: `G₁ ω = Ψ ωᵀ Q ω` has full column rank a.s.;
* `hG`: `E‖G₁†G₂(Q⊥ᵀE)‖_F² = E[(q/(s−q−1)) ‖E‖_F²]` with `E = (I − QQᵀ)A` — the end of the
  proof of `lem:completion` (`lem:moments` conditionally on `(Ω, G₁)`, `‖Q⊥ᵀE‖_F = ‖E‖_F`,
  `lem:invmom`) integrated over `Ω`.
Other hypotheses as in `gn_main`.
Atlas `gn-expected-error` (uses `rsvd-expected-error`, `sketched-regression`,
`orthonormal-completion`). -/
theorem gn_main_of_completion [IsProbabilityMeasure μ] [DecidableEq m]
    {A : Matrix m n ℝ} {U₁ : Matrix m (Fin k) ℝ} {U₂ : Matrix m r ℝ}
    {V₁ : Matrix n (Fin k) ℝ} {V₂ : Matrix n r' ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t) (hts : t + 2 ≤ s) (hqt : q ≤ t)
    (Ω : Ωs → Matrix n (Fin t) ℝ) (Ψ : Ωs → Matrix m (Fin s) ℝ)
    (Q : Ωs → Matrix m (Fin q) ℝ)
    {rp : Type*} [Fintype rp] (Qp : Ωs → Matrix m rp ℝ)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω)
    (hcomp : ∀ᵐ ω ∂μ, Q ω * (Q ω)ᵀ + Qp ω * (Qp ω)ᵀ = 1)
    (hunit : ∀ᵐ ω ∂μ, IsUnit ((V₁ᵀ * Ω ω) * (V₁ᵀ * Ω ω)ᵀ))
    (hG₁ : ∀ᵐ ω ∂μ, IsUnit (((Ψ ω)ᵀ * Q ω)ᵀ * ((Ψ ω)ᵀ * Q ω)))
    (hinv : ∫ ω, frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ∂μ
      = (k : ℝ) / (t - k - 1) * frobSq S₂)
    (hG : ∫ ω, frobSq (pinvL ((Ψ ω)ᵀ * Q ω) * ((Ψ ω)ᵀ * Qp ω) * ((Qp ω)ᵀ * residual (Q ω) A)) ∂μ
      = ∫ ω, (q : ℝ) / (s - q - 1) * frobSq (residual (Q ω) A) ∂μ)
    (hYi : Integrable (fun ω => frobSq (residual (Q ω) A)) μ)
    (hGi : Integrable (fun ω =>
      frobSq (pinvL ((Ψ ω)ᵀ * Q ω) * ((Ψ ω)ᵀ * Qp ω) * ((Qp ω)ᵀ * residual (Q ω) A))) μ)
    (hZi : Integrable (fun ω => frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) μ) :
    ∫ ω, frobSq (A - sketchedOutput (Q ω) (Ψ ω) A) ∂μ
      ≤ (1 + (t : ℝ) / (s - t - 1)) * ((1 + (k : ℝ) / (t - k - 1)) * frobSq S₂) := by
  have hae : (fun ω => frobSq (A - sketchedOutput (Q ω) (Ψ ω) A)) =ᵐ[μ]
      fun ω => frobSq (residual (Q ω) A)
        + frobSq (pinvL ((Ψ ω)ᵀ * Q ω) * ((Ψ ω)ᵀ * Qp ω) * ((Qp ω)ᵀ * residual (Q ω) A)) := by
    filter_upwards [hQo, hcomp, hG₁] with ω h1 h2 h3
    exact frobSq_error (Q ω) (Qp ω) (Ψ ω) A h1 h2 h3
  have hcond : ∫ ω, frobSq (A - sketchedOutput (Q ω) (Ψ ω) A) ∂μ
      = ∫ ω, (1 + (q : ℝ) / (s - q - 1)) * frobSq (residual (Q ω) A) ∂μ := by
    rw [integral_congr_ae hae, integral_add hYi hGi, hG, ← integral_add hYi (hYi.const_mul _)]
    congr 1
    ext ω
    ring
  exact gn_main hA hU₂ hV₁ hV₂ hV hkt hts hqt Ω Ψ Q hQo hQr hunit hinv hcond hYi hZi

end Main

end NLAlib

end
