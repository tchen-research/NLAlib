import NLAlib.Matrix.Spectral.DiagonalDominanceStability
/-!
# Positive-diagonal and Hermitian dominance corollaries

These expose the source's absolute diagonal-dominance hypotheses directly,
for both real symmetric and complex Hermitian matrices.
Source: Horn–Johnson (2013), Corollaries 6.1.8, 7.2.3 and 6.2.27.
-/
noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complex number with zero imaginary part and positive real part has
norm equal to its real part; this translates the positive diagonal in the
Gershgorin dominance corollaries. -/
theorem norm_eq_re_of_im_eq_zero_of_re_pos {z : ℂ} (hi : z.im = 0) (hr : 0 < z.re) :
    ‖z‖ = z.re := by
  have hz : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
  calc
    ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hz
    _ = z.re := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- Strict absolute row dominance and positive real diagonal place every
complex eigenvalue in the open right half-plane. Source: Horn–Johnson
(2013), Corollary 6.1.8; arbitrary nonsymmetric matrices are allowed.
atlas: gershgorin-diagonal-dominance -/
theorem re_pos_of_mem_spectrum_of_strict_diagonal_dominance
    {A : Matrix n n ℂ} (hdiag : ∀ i, (A i i).im = 0)
    (hpos : ∀ i, 0 < (A i i).re)
    (hstrict : ∀ i, gershgorinRowRadius A i < ‖A i i‖)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) : 0 < μ.re := by
  apply re_pos_of_mem_spectrum_of_row_radius_lt_re_diag _ hμ
  intro i
  simpa only [norm_eq_re_of_im_eq_zero_of_re_pos (hdiag i) (hpos i)] using hstrict i

/-- Strict absolute row dominance with positive diagonal makes a real
symmetric matrix positive definite. Source: Horn–Johnson (2013),
Corollary 7.2.3; no nonempty-dimension assumption is needed.
atlas: gershgorin-diagonal-dominance -/
theorem posDef_of_isHermitian_of_strict_diagonal_dominance
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (hpos : ∀ i, 0 < A i i)
    (hstrict : ∀ i, gershgorinRowRadius A i < ‖A i i‖) : A.PosDef := by
  apply posDef_of_isHermitian_of_row_radius_lt_diag hA
  intro i
  simpa only [Real.norm_eq_abs, abs_of_pos (hpos i)] using hstrict i

/-- Strict absolute row dominance and positive real diagonal also make a
complex Hermitian matrix positive definite. Source: Horn–Johnson (2013),
Corollary 7.2.3; the real-symmetric conclusion extends verbatim.
atlas: gershgorin-diagonal-dominance -/
theorem posDef_of_isHermitian_of_strict_diagonal_dominance_complex
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hdiag : ∀ i, (A i i).im = 0) (hpos : ∀ i, 0 < (A i i).re)
    (hstrict : ∀ i, gershgorinRowRadius A i < ‖A i i‖) : A.PosDef := by
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hmem : (hA.eigenvalues i : ℂ) ∈ spectrum ℂ A :=
    spectrum.algebraMap_mem ℂ (hA.eigenvalues_mem_spectrum_real i)
  exact re_pos_of_mem_spectrum_of_strict_diagonal_dominance hdiag hpos hstrict hmem

/-- Irreducible weak absolute row dominance with positive real diagonal
and a strict row makes a complex Hermitian matrix positive definite.
Source: Horn–Johnson (2013), Corollary 6.2.27; the strict-row hypothesis
is necessary and is explicit.
atlas: gershgorin-diagonal-dominance -/
theorem posDef_of_isHermitian_of_irreducible_weak_diagonal_dominance_complex
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hIrred : (A.map norm).IsIrreducible)
    (hdiag : ∀ i, (A i i).im = 0) (hpos : ∀ i, 0 < (A i i).re)
    (hweak : ∀ i, gershgorinRowRadius A i ≤ ‖A i i‖)
    (hstrict : ∃ i, gershgorinRowRadius A i < ‖A i i‖) : A.PosDef := by
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hmem : (hA.eigenvalues i : ℂ) ∈ spectrum ℂ A :=
    spectrum.algebraMap_mem ℂ (hA.eigenvalues_mem_spectrum_real i)
  exact re_pos_of_mem_spectrum_of_irreducible_weak_diagonal_dominance
    hIrred hdiag hpos hweak hstrict hmem

end NLAlib
