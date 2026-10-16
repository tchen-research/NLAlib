import NLAlib.Matrix.Spectral.EigenvectorSpectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Complex spectral bounds from positive subsolutions

A weighted maximum-coordinate argument bounds every complex eigenvalue of a
matrix dominated entrywise in modulus by a nonnegative real matrix. This is
the comparison mechanism behind Perron theory and Collatz certificates.
Source: Horn–Johnson, Matrix Analysis, Chapter 8.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
/-- A positive subsolution controls every eigenvalue of every complex matrix
dominated by the nonnegative comparison matrix.
Source: Horn–Johnson, Chapter 8.
atlas: collatz-wielandt-certificates (partial) -/
theorem norm_eigenvalue_le_of_abs_le_of_positive_subsolution
    {A : Matrix ι ι ℝ} {B : Matrix ι ι ℂ} (hBA : ∀ i j, norm (B i j) ≤ A i j)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) {r : ℝ}
    (hAp : ∀ i, (A *ᵥ p) i ≤ r * p i)
    {μ : ℂ} {z : ι → ℂ} (hz : z ≠ 0) (hBz : B *ᵥ z = μ • z) : ‖μ‖ ≤ r := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
  have hzj : 0 < ‖z j‖ := norm_pos_iff.mpr hj
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun k => ‖z k‖ / p k)
    Finset.univ_nonempty
  let t : ℝ := ‖z i‖ / p i
  have ht : 0 < t := (div_pos hzj (hp j)).trans_le (hi j (mem_univ j))
  have hzi : ‖z i‖ = t * p i := by
    dsimp [t]
    field_simp [(hp i).ne']
  have hzle (k : ι) : ‖z k‖ ≤ t * p k :=
    (div_le_iff₀ (hp k)).mp (hi k (mem_univ k))
  have hAi (k : ι) : 0 ≤ A i k := (norm_nonneg _).trans (hBA i k)
  have hnorm : ‖μ‖ * ‖z i‖ ≤ t * (r * p i) := by
    calc
      ‖μ‖ * ‖z i‖ = ‖(B *ᵥ z) i‖ := by rw [hBz]; simp
      _ ≤ ∑ k, ‖B i k * z k‖ := norm_sum_le _ _
      _ = ∑ k, ‖B i k‖ * ‖z k‖ := by simp only [norm_mul]
      _ ≤ ∑ k, A i k * (t * p k) := Finset.sum_le_sum fun k _ =>
        mul_le_mul (hBA i k) (hzle k) (norm_nonneg _) (hAi k)
      _ = t * (A *ᵥ p) i := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        congr 1
        funext k
        ring
      _ ≤ t * (r * p i) := mul_le_mul_of_nonneg_left (hAp i) ht.le
  rw [hzi] at hnorm
  have htp : 0 < t * p i := mul_pos ht (hp i)
  exact (mul_le_mul_iff_left₀ htp).mp (by nlinarith [hnorm])

/-- A positive subsolution bounds the entire complex spectral radius.
No real-spectrum or diagonalizability assumption is used.
Source: Horn–Johnson, Chapter 8.
atlas: collatz-wielandt-certificates (partial) -/
theorem spectralRadius_le_of_abs_le_of_positive_subsolution
    {A : Matrix ι ι ℝ} {B : Matrix ι ι ℂ} (hBA : ∀ i j, norm (B i j) ≤ A i j)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) {r : ℝ}
    (hAp : ∀ i, (A *ᵥ p) i ≤ r * p i) :
    spectralRadius ℂ B ≤ ENNReal.ofReal r := by
  unfold spectralRadius
  apply iSup₂_le
  intro μ hμ
  obtain ⟨z, hz, hBz⟩ := NLAlib.exists_mulVec_eq_smul_of_mem_spectrum hμ
  have hnorm := norm_eigenvalue_le_of_abs_le_of_positive_subsolution hBA hp hAp hz hBz
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hnorm

end Matrix
