import NLAlib.Matrix.Spectral.ThinSingularFunctions
import NLAlib.Matrix.Spectral.Core

/-! # Largest Hermitian eigenvalue, trace and spectral norm

Finite spectral coordinates give trace positivity detection and identify
the largest eigenvalue with the spectral norm for PSD matrices. Real-spectrum
transport in a supplied unitary basis also supports tensor amplification.
Source: Horn–Johnson, §4.1 and §5.6.
-/
noncomputable section
open Matrix Finset
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A real or complex Hermitian matrix has spectral norm equal to the supremum norm of
its real eigenvalues, including empty dimensions. -/
theorem _root_.Matrix.IsHermitian.specNorm_eq_norm_eigenvalues
    {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    specNorm A = ‖hA.eigenvalues‖ := by
  let U : Matrix n n 𝕜 := hA.eigenvectorUnitary
  have hU : HasOrthonormalCols U := by
    change Uᴴ * U = 1
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have he : A = thinSingularMatrix U U hA.eigenvalues := by
    simpa only [thinSingularMatrix, U, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def] using hA.spectral_theorem
  calc
    specNorm A = specNorm (thinSingularMatrix U U hA.eigenvalues) := congrArg specNorm he
    _ = _ := specNorm_thinSingularMatrix U U hU hU _

/-- Every real eigenvalue is bounded above by the largest Hermitian eigenvalue. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_le_lambdaMax {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (i : n) : hA.eigenvalues i ≤ lambdaMax A := by
  apply le_csSup
  · rw [hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).bddAbove
  · exact hA.eigenvalues_mem_spectrum_real i

/-- A nonnegative real trace forces a nonnegative largest eigenvalue. -/
theorem _root_.Matrix.IsHermitian.lambdaMax_nonneg_of_trace_re_nonneg [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (htr : 0 ≤ A.trace.re) : 0 ≤ lambdaMax A := by
  by_contra hn
  have hsum : (∑ i, hA.eigenvalues i) < 0 :=
    Finset.sum_neg (fun i _ => (hA.eigenvalue_le_lambdaMax i).trans_lt (lt_of_not_ge hn))
      Finset.univ_nonempty
  have he : A.trace.re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]
    simp
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The largest Hermitian eigenvalue is at most its spectral norm. -/
theorem _root_.Matrix.IsHermitian.lambdaMax_le_specNorm [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : lambdaMax A ≤ specNorm A := by
  rw [hA.specNorm_eq_norm_eigenvalues, lambdaMax, hA.spectrum_real_eq_range_eigenvalues]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i, rfl⟩
  exact (le_abs_self _).trans (norm_le_pi_norm hA.eigenvalues i)

open scoped Matrix.Norms.L2Operator in
/-- A complex PSD matrix's largest eigenvalue equals its spectral norm. -/
theorem _root_.Matrix.PosSemidef.lambdaMax_eq_specNorm [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : lambdaMax A = specNorm A := by
  apply le_antisymm hA.isHermitian.lambdaMax_le_specNorm
  rw [hA.isHermitian.specNorm_eq_norm_eigenvalues]
  have hmax : 0 ≤ lambdaMax A :=
    (hA.eigenvalues_nonneg (Classical.choice inferInstance)).trans
      (hA.isHermitian.eigenvalue_le_lambdaMax _)
  apply (pi_norm_le_iff_of_nonneg hmax).mpr
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)] using
    hA.isHermitian.eigenvalue_le_lambdaMax i

/-- A real diagonal in a complex matrix has exactly the corresponding real spectrum. -/
theorem spectrum_real_diagonal_ofReal (d : n → ℝ) :
    spectrum ℝ (diagonal fun i => (d i : ℂ)) = Set.range d := by
  ext x
  rw [← spectrum.algebraMap_mem_iff ℂ, spectrum_diagonal]
  change (∃ i, (d i : ℂ) = (x : ℂ)) ↔ ∃ i, d i = x
  simp only [Complex.ofReal_inj]

/-- A supplied square unitary diagonalization identifies the entire real spectrum. -/
theorem spectrum_real_thinSingularMatrix (U : Matrix n n ℂ)
    (hU : HasOrthonormalCols U) (d : n → ℝ) :
    spectrum ℝ (thinSingularMatrix U U d) = Set.range d := by
  let W : Matrix.unitaryGroup n ℂ := ⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩
  have he : spectrum ℝ ((W : Matrix n n ℂ) * (diagonal fun i => (d i : ℂ)) *
      (W : Matrix n n ℂ)ᴴ) = spectrum ℝ (diagonal fun i => (d i : ℂ)) :=
    AlgEquiv.spectrum_eq
      (Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) W).toAlgEquiv (diagonal fun i => (d i : ℂ))
  change spectrum ℝ (U * (diagonal fun i => (d i : ℂ)) * Uᴴ) = Set.range d
  exact he.trans (spectrum_real_diagonal_ofReal d)

end NLAlib
