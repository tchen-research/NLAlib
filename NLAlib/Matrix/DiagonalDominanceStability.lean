import NLAlib.Matrix.IrreducibleDiagonalDominance
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive stability and definiteness from diagonal dominance

Closed discs with nonnegative real centers meet the imaginary axis only at
zero. Strict dominance excludes zero directly; Taussky excludes it under
irreducibility, weak dominance, and at least one strict row.
Source: Horn–Johnson (2013), Corollaries 6.1.8, 7.2.3 and 6.2.27.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complex spectral point has positive real part when every row radius
is smaller than the real part of the diagonal. Source: Horn–Johnson (2013),
Corollary 6.1.8; this form also allows nonreal diagonal entries.
atlas: gershgorin-diagonal-dominance (partial) -/
theorem re_pos_of_mem_spectrum_of_row_radius_lt_re_diag
    {A : Matrix n n ℂ} (hA : ∀ i, gershgorinRowRadius A i < (A i i).re)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) : 0 < μ.re := by
  obtain ⟨i, hi⟩ := exists_mem_gershgorinRowDisc_of_mem_spectrum hμ
  have hnorm : ‖A i i - μ‖ ≤ gershgorinRowRadius A i := by
    simpa only [gershgorinRowDisc, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hi
  have hre := (Complex.re_le_norm (A i i - μ)).trans hnorm
  simp only [Complex.sub_re] at hre
  linarith [hA i]

/-- A closed disc centered at a nonnegative real number and with radius at
most that center meets the closed left half-plane only at zero. This is
the geometric boundary step in the Taussky positive-stability corollary. -/
theorem eq_zero_of_norm_sub_real_le_of_re_nonpos {z : ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hz : ‖z - (d : ℂ)‖ ≤ d) (hre : z.re ≤ 0) : z = 0 := by
  have hs : ‖z - (d : ℂ)‖ ^ 2 ≤ d ^ 2 := sq_le_sq₀ (norm_nonneg _) hd |>.mpr hz
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hs
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hs
  have hprod : 0 ≤ -(2 * z.re * d) :=
    neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hre) hd)
  have hr : z.re = 0 := by nlinarith [sq_nonneg z.im, sq_nonneg z.re]
  have hi : z.im = 0 := by rw [hr] at hs; nlinarith [sq_nonneg z.im]
  exact Complex.ext hr hi

/-- Weak row dominance about nonnegative real diagonal entries gives
positive real parts whenever the matrix is nonsingular. Source:
Horn–Johnson (2013), Corollary 6.2.27; the only boundary point of a disc
on the imaginary axis is zero. -/
theorem re_pos_of_mem_spectrum_of_isUnit_of_weak_diagonal_dominance
    {A : Matrix n n ℂ} (hunit : IsUnit A)
    (hdiag : ∀ i, (A i i).im = 0)
    (hweak : ∀ i, gershgorinRowRadius A i ≤ (A i i).re)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) : 0 < μ.re := by
  by_contra! hnonpos
  obtain ⟨i, hi⟩ := exists_mem_gershgorinRowDisc_of_mem_spectrum hμ
  have hd : A i i = ((A i i).re : ℂ) := by
    apply Complex.ext <;> simp [hdiag i]
  have hnorm : ‖μ - ((A i i).re : ℂ)‖ ≤ (A i i).re := by
    have : ‖μ - A i i‖ ≤ gershgorinRowRadius A i := by
      simpa only [gershgorinRowDisc, Metric.mem_closedBall, dist_eq_norm] using hi
    rw [hd] at this
    exact this.trans (hweak i)
  have hzero := eq_zero_of_norm_sub_real_le_of_re_nonpos
    ((gershgorinRowRadius_nonneg A i).trans (hweak i)) hnorm hnonpos
  exact spectrum.zero_notMem ℂ hunit (hzero ▸ hμ)

/-- Positive real diagonal and irreducible weak row dominance, with one
strict row, imply that every complex eigenvalue has positive real part.
Source: Horn–Johnson (2013), Corollary 6.2.27; the strict-row assumption is
necessary and is retained explicitly.
atlas: gershgorin-diagonal-dominance (partial) -/
theorem re_pos_of_mem_spectrum_of_irreducible_weak_diagonal_dominance
    {A : Matrix n n ℂ} (hIrred : (A.map norm).IsIrreducible)
    (hdiag : ∀ i, (A i i).im = 0) (hpos : ∀ i, 0 < (A i i).re)
    (hweak : ∀ i, gershgorinRowRadius A i ≤ ‖A i i‖)
    (hstrict : ∃ i, gershgorinRowRadius A i < ‖A i i‖)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) : 0 < μ.re := by
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr
    (isUnit_iff_ne_zero.mpr (det_ne_zero_of_irreducible_weak_diagonal_dominance A hIrred hweak hstrict))
  apply re_pos_of_mem_spectrum_of_isUnit_of_weak_diagonal_dominance hunit hdiag _ hμ
  intro i
  have hd : A i i = ((A i i).re : ℂ) := by apply Complex.ext <;> simp [hdiag i]
  have hn : ‖A i i‖ = (A i i).re := by
    calc
      ‖A i i‖ = ‖((A i i).re : ℂ)‖ := congrArg norm hd
      _ = (A i i).re := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos i)]
  simpa only [hn] using hweak i

/-- A real symmetric matrix with strictly dominant positive diagonal is
positive definite. Source: Horn–Johnson (2013), Corollary 7.2.3; the radius
inequality already implies positivity of the diagonal, including the
vacuous zero-dimensional case.
atlas: gershgorin-diagonal-dominance (partial) -/
theorem posDef_of_isHermitian_of_row_radius_lt_diag {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hstrict : ∀ i, gershgorinRowRadius A i < A i i) : A.PosDef := by
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro j
  obtain ⟨i, hi⟩ := exists_mem_gershgorinRowDisc_of_mem_spectrum (hA.eigenvalues_mem_spectrum_real j)
  have hb : A i i - hA.eigenvalues j ≤ gershgorinRowRadius A i := by
    have hn : ‖hA.eigenvalues j - A i i‖ ≤ gershgorinRowRadius A i := hi
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, abs_sub_comm] using hn)
  linarith [hstrict i]

/-- An irreducible real symmetric weakly diagonally dominant matrix with
positive diagonal and at least one strict row is positive definite.
Source: Horn–Johnson (2013), Corollary 6.2.27; the graph is that of the
entrywise absolute values and the strict-row repair is explicit.
atlas: gershgorin-diagonal-dominance (partial) -/
theorem posDef_of_isHermitian_of_irreducible_weak_diagonal_dominance
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (hIrred : (A.map norm).IsIrreducible)
    (hpos : ∀ i, 0 < A i i)
    (hweak : ∀ i, gershgorinRowRadius A i ≤ ‖A i i‖)
    (hstrict : ∃ i, gershgorinRowRadius A i < ‖A i i‖) : A.PosDef := by
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr
    (isUnit_iff_ne_zero.mpr (det_ne_zero_of_irreducible_weak_diagonal_dominance A hIrred hweak hstrict))
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro j
  have hμ := hA.eigenvalues_mem_spectrum_real j
  obtain ⟨i, hi⟩ := exists_mem_gershgorinRowDisc_of_mem_spectrum hμ
  have hb : A i i - hA.eigenvalues j ≤ gershgorinRowRadius A i := by
    have hn : ‖hA.eigenvalues j - A i i‖ ≤ gershgorinRowRadius A i := hi
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, abs_sub_comm] using hn)
  have hw : gershgorinRowRadius A i ≤ A i i := by
    simpa only [Real.norm_eq_abs, abs_of_pos (hpos i)] using hweak i
  have hnonneg : 0 ≤ hA.eigenvalues j := by linarith
  have hne : hA.eigenvalues j ≠ 0 := by
    intro heq
    exact spectrum.zero_notMem ℝ hunit (heq ▸ hμ)
  exact lt_of_le_of_ne hnonneg hne.symm

end NLAlib
