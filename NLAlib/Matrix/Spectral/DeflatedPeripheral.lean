import NLAlib.Matrix.Spectral.EigenvalueSimplicity
import NLAlib.Matrix.Spectral.MatrixPowerReal
import NLAlib.Matrix.Spectral.EigenvectorSpectrum

/-! # Spectral gap after a simple peripheral eigenline is removed

Paired left and right eigenvectors define a commuting rank-one projector.
If their simple positive eigenvalue is the only peripheral value, the
normalized deflated matrix has spectral radius strictly below one.
Source: Horn–Johnson, Matrix Analysis, Chapters 5 and 8.
-/
noncomputable section
open Matrix Finset
open scoped Matrix
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open scoped Matrix.Norms.L2Operator in
/-- Removing a simple, uniquely peripheral positive eigenline gives a strict
spectral gap, also for nonsymmetric and nonnormal matrices.
Source: Horn–Johnson, Chapters 5 and 8.
atlas: primitive-perron-power-limit (partial) -/
theorem deflated_spectralRadius_lt_one_of_simple_unique_peripheral
    (A : Matrix ι ι ℂ) {p q : ι → ℂ} {r : ℝ} (hr : 0 < r)
    (hp : p ≠ 0) (hpair : q ⬝ᵥ p ≠ 0)
    (hAp : A *ᵥ p = (r : ℂ) • p) (hqA : q ᵥ* A = (r : ℂ) • q)
    (hsimple : A.charpoly.rootMultiplicity (r : ℂ) = 1)
    (hbound : ∀ μ ∈ spectrum ℂ A, ‖μ‖ ≤ r)
    (hperipheral : ∀ μ ∈ spectrum ℂ A, ‖μ‖ = r → μ = (r : ℂ)) :
    spectralRadius ℂ ((r : ℂ)⁻¹ • A - (q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q) < 1 := by
  let P := (q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q
  let T := (r : ℂ)⁻¹ • A
  let Q := T - P
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hPP : P * P = P := normalized_vecMulVec_mul_self hpair
  have hAP : A * P = (r : ℂ) • P := (mul_normalized_vecMulVec_eq_smul hAp hqA).1
  have hPA : P * A = (r : ℂ) • P := (mul_normalized_vecMulVec_eq_smul hAp hqA).2
  have hTP : T * P = P := by
    change ((r : ℂ)⁻¹ • A) * P = P
    rw [Matrix.smul_mul, hAP, smul_smul, inv_mul_cancel₀ hrC, one_smul]
  have hPT : P * T = P := by
    change P * ((r : ℂ)⁻¹ • A) = P
    rw [Matrix.mul_smul, hPA, smul_smul, inv_mul_cancel₀ hrC, one_smul]
  have hPQ : P * Q = 0 := by
    change P * (T - P) = 0
    rw [Matrix.mul_sub, hPT, hPP, sub_self]
  have hPp : P *ᵥ p = p := by
    ext i
    simp only [P, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, Pi.smul_apply, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    field_simp [hpair]
  have hspanle : ℂ ∙ p ≤ Module.End.eigenspace A.toLin' (r : ℂ) :=
    (Submodule.span_singleton_le_iff_mem p _).mpr (Module.End.mem_eigenspace_iff.mpr hAp)
  have hdimle := LinearMap.finrank_eigenspace_le A.toLin' (r : ℂ)
  rw [Matrix.charpoly_toLin', hsimple] at hdimle
  have hdimge := Submodule.finrank_mono hspanle
  rw [finrank_span_singleton hp] at hdimge
  have hspan : ℂ ∙ p = Module.End.eigenspace A.toLin' (r : ℂ) :=
    Submodule.eq_of_le_of_finrank_eq hspanle (by rw [finrank_span_singleton hp]; omega)
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro μ hμ
  have hμreal : ‖μ‖ < (1 : ℝ) := by
    by_cases hμ0 : μ = 0
    · simp [hμ0]
    obtain ⟨z, hz, hQz⟩ := exists_mulVec_eq_smul_of_mem_spectrum hμ
    have hPz0 : P *ᵥ z = 0 := by
      have hzero : μ • (P *ᵥ z) = 0 := by
        rw [← Matrix.mulVec_smul, ← hQz, Matrix.mulVec_mulVec, hPQ, Matrix.zero_mulVec]
      exact (smul_eq_zero.mp hzero).resolve_left hμ0
    have hTz : T *ᵥ z = μ • z := by
      change (T - P) *ᵥ z = μ • z at hQz
      simpa only [Matrix.sub_mulVec, hPz0, sub_zero] using hQz
    have hAeq : A = (r : ℂ) • T := by
      change A = (r : ℂ) • ((r : ℂ)⁻¹ • A)
      rw [smul_smul, mul_inv_cancel₀ hrC, one_smul]
    have hAz : A *ᵥ z = ((r : ℂ) * μ) • z := by
      rw [hAeq, Matrix.smul_mulVec, hTz, smul_smul]
    have hAzmem := Matrix.mem_spectrum_of_mulVec_eq_smul hz hAz
    have hnorm := hbound _ hAzmem
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hnorm
    have hnorm1 : ‖μ‖ ≤ 1 := by nlinarith
    by_contra! hnot
    have heq1 : ‖μ‖ = 1 := le_antisymm hnorm1 hnot
    have hper := hperipheral _ hAzmem (by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, heq1, mul_one])
    have hμ1 : μ = 1 := mul_left_cancel₀ hrC (by simpa only [mul_one] using hper)
    have hmem : z ∈ Module.End.eigenspace A.toLin' (r : ℂ) :=
      Module.End.mem_eigenspace_iff.mpr (by
        change A *ᵥ z = _
        simpa only [hμ1, mul_one] using hAz)
    rw [← hspan] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hPz : P *ᵥ z = z := by rw [← hc, Matrix.mulVec_smul, hPp]
    exact hz (hPz.symm.trans hPz0)
  exact_mod_cast hμreal

end NLAlib
