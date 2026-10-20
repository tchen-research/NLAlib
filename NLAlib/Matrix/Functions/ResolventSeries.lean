import NLAlib.Matrix.Functions.HermitianResolvent
import NLAlib.ForMathlib.Analysis.Normed.Algebra.ResolventSeries
import NLAlib.ForMathlib.Analysis.Normed.Algebra.SeriesProducts

/-!
# Neumann series under the sharp Hermitian resolvent height condition

The generic convergent expansion specializes to the sharp spectral-norm
condition for a Hermitian base. The perturbation may be any matrix.
The actual finite-word expansion retains every coefficient on its original
side and proves joint absolute summability. Empty words and empty matrix
dimensions are included.

Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Lemma 6.9.
These are deterministic prerequisites for the
`independent-sum-spectrum-universality` card.
-/

noncomputable section
open scoped Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Sharp imaginary height implies the genuine Neumann contraction. -/
theorem _root_.Matrix.IsHermitian.norm_resolvent_mul_lt_one
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    {H : Matrix n n ℂ} (hH : specNorm H < |z.im|) :
    ‖resolvent A z * H‖ < 1 := by
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  calc
    ‖resolvent A z * H‖ ≤ specNorm (resolvent A z) * specNorm H := norm_mul_le _ _
    _ ≤ |z.im|⁻¹ * specNorm H :=
      mul_le_mul_of_nonneg_right (hA.specNorm_resolvent_le hz) (specNorm_nonneg _)
    _ < |z.im|⁻¹ * |z.im| := mul_lt_mul_of_pos_left hH (inv_pos.mpr hpos)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- The perturbed native resolvent is the actual convergent ordered Neumann
series whenever the perturbation is smaller than the imaginary height. -/
theorem _root_.Matrix.IsHermitian.hasSum_resolvent_add
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    {H : Matrix n n ℂ} (hH : specNorm H < |z.im|) :
    HasSum (fun k : ℕ => (resolvent A z * H) ^ k * resolvent A z)
      (resolvent (A + H) z) := by
  have hu : z ∈ resolventSet ℂ A := by
    simpa only [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] using
      hA.isUnit_smul_one_sub_of_im_ne_zero hz
  exact spectrum.hasSum_resolvent_add_of_norm_mul_lt_one hu
    (hA.norm_resolvent_mul_lt_one hz hH)

/-- The sharp-height native matrix series is absolutely summable. -/
theorem _root_.Matrix.IsHermitian.summable_norm_resolvent_add_series
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    {H : Matrix n n ℂ} (hH : specNorm H < |z.im|) :
    Summable (fun k : ℕ => ‖(resolvent A z * H) ^ k * resolvent A z‖) :=
  spectrum.summable_norm_resolvent_add_series (hA.norm_resolvent_mul_lt_one hz hH)

end NLAlib

noncomputable section
open scoped Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual profile expansion is jointly absolutely summable and sums to
the literal shifted word, in its original matrix multiplication order. -/
theorem _root_.Matrix.IsHermitian.summable_norm_and_hasSum_resolventWord_add
    {m : ℕ} {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : Fin m → ℂ × Matrix n n ℂ) (hw : ∀ j, (w j).1.im ≠ 0)
    {H : Matrix n n ℂ} (hH : ∀ j, specNorm H < |(w j).1.im|) :
    Summable (fun t : Fin m → ℕ =>
      ‖(List.ofFn (fun j =>
        (resolvent A (w j).1 * H) ^ (t j) * resolvent A (w j).1 * (w j).2)).prod‖) ∧
    HasSum (fun t : Fin m → ℕ =>
      (List.ofFn (fun j =>
        (resolvent A (w j).1 * H) ^ (t j) * resolvent A (w j).1 * (w j).2)).prod)
      (List.ofFn (fun j => resolvent (A + H) (w j).1 * (w j).2)).prod := by
  let f : Fin m → ℕ → Matrix n n ℂ := fun j k =>
    (resolvent A (w j).1 * H) ^ k * resolvent A (w j).1 * (w j).2
  let x : Fin m → Matrix n n ℂ := fun j => resolvent (A + H) (w j).1 * (w j).2
  have hs : ∀ j, HasSum (f j) (x j) := by
    intro j
    exact (hA.hasSum_resolvent_add (hw j) (hH j)).mul_right (w j).2
  have hn : ∀ j, Summable (fun k => ‖f j k‖) := by
    intro j
    have ht := (hA.summable_norm_resolvent_add_series (hw j) (hH j)).mul_right ‖(w j).2‖
    exact ht.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_mul_le _ _)
  exact ⟨summable_norm_list_prod_of_summable_norm f hn,
    hasSum_list_prod_of_summable_norm f x hs hn⟩

end NLAlib
