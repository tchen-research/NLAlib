import NLAlib.Matrix.Spectral.NumericalRange
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Bilinear square energy on closed Euclidean unit balls

The supremum uses two actual complex Euclidean closed unit balls. It is a
maximum even in empty dimension, because the zero vectors are always allowed.
This is the deterministic bilinear part of the variance proxy in source
arXiv:2201.05142v3, Lemmas5.7--5.9, for independent-sum spectral universality.
-/

noncomputable section
set_option autoImplicit false
open Matrix Finset
open scoped Matrix
namespace NLAlib

variable {ι n : Type*} [Fintype n]

/-- The actual bilinear square-energy supremum for the selected summands,
using complex Euclidean unit balls and the full modulus squared. -/
def bilinearSquareMass (D : ι → Matrix n n ℂ) (s : Finset ι) : ℝ :=
  sSup ((fun v : EuclideanSpace ℂ n × EuclideanSpace ℂ n =>
    ∑ i ∈ s, ‖star v.1.ofLp ⬝ᵥ (D i *ᵥ v.2.ofLp)‖ ^ 2) ''
      (Metric.closedBall (0 : EuclideanSpace ℂ n) 1 ×ˢ Metric.closedBall (0 : EuclideanSpace ℂ n) 1))

private theorem continuous_bilinearSquareMass_integrand (s : Finset ι) :
    Continuous (fun p : (ι → Matrix n n ℂ) ×
        (EuclideanSpace ℂ n × EuclideanSpace ℂ n) =>
      ∑ i ∈ s, ‖star p.2.1.ofLp ⬝ᵥ (p.1 i *ᵥ p.2.2.ofLp)‖ ^ 2) := by
  have hv : Continuous (fun p : (ι → Matrix n n ℂ) ×
      (EuclideanSpace ℂ n × EuclideanSpace ℂ n) => p.2.1.ofLp) :=
    (PiLp.continuous_ofLp 2 (fun _ : n => ℂ)).comp continuous_snd.fst
  have hw : Continuous (fun p : (ι → Matrix n n ℂ) ×
      (EuclideanSpace ℂ n × EuclideanSpace ℂ n) => p.2.2.ofLp) :=
    (PiLp.continuous_ofLp 2 (fun _ : n => ℂ)).comp continuous_snd.snd
  apply continuous_finsetSum
  intro i _
  exact (hv.star.dotProduct (((continuous_apply i).comp continuous_fst).matrix_mulVec hw)).norm.pow 2

/-- The actual supremum varies continuously with all complex matrix entries. -/
theorem continuous_bilinearSquareMass (s : Finset ι) :
    Continuous (fun D : ι → Matrix n n ℂ => bilinearSquareMass D s) := by
  exact ((isCompact_closedBall (0 : EuclideanSpace ℂ n) 1).prod
    (isCompact_closedBall (0 : EuclideanSpace ℂ n) 1)).continuous_sSup
      (continuous_bilinearSquareMass_integrand s)

/-- Measurability follows from the native continuous maximum representation. -/
theorem measurable_bilinearSquareMass [Fintype ι] (s : Finset ι) :
    Measurable (fun D : ι → Matrix n n ℂ => bilinearSquareMass D s) := by
  let : SecondCountableTopology (Matrix n n ℂ) :=
    inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  exact (continuous_bilinearSquareMass s).measurable

/-- A single actual pair of probes simultaneously attains the full sum. -/
theorem exists_bilinearSquareMass_eq (D : ι → Matrix n n ℂ) (s : Finset ι) :
    ∃ v w : EuclideanSpace ℂ n, ‖v‖ ≤ 1 ∧ ‖w‖ ≤ 1 ∧
      bilinearSquareMass D s = ∑ i ∈ s, ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2 := by
  have hne : (Metric.closedBall (0 : EuclideanSpace ℂ n) 1 ×ˢ
      Metric.closedBall (0 : EuclideanSpace ℂ n) 1).Nonempty := ⟨(0, 0), by simp⟩
  obtain ⟨⟨v, w⟩, hvw, he⟩ :=
    ((isCompact_closedBall (0 : EuclideanSpace ℂ n) 1).prod
      (isCompact_closedBall (0 : EuclideanSpace ℂ n) 1)).exists_sSup_image_eq hne
      (((continuous_bilinearSquareMass_integrand s).comp
        (continuous_const.prodMk continuous_id)).continuousOn)
  exact ⟨v, w, by simpa using hvw.1, by simpa using hvw.2, he⟩

/-- Every admissible probe lies below the actual attained supremum. -/
theorem sum_bilinear_sq_le_bilinearSquareMass (D : ι → Matrix n n ℂ) (s : Finset ι)
    (v w : EuclideanSpace ℂ n) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ∑ i ∈ s, ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2 ≤ bilinearSquareMass D s := by
  apply le_csSup
  · exact (((isCompact_closedBall (0 : EuclideanSpace ℂ n) 1).prod
      (isCompact_closedBall (0 : EuclideanSpace ℂ n) 1)).image
        ((continuous_bilinearSquareMass_integrand s).comp
          (continuous_const.prodMk continuous_id))).bddAbove
  · exact ⟨(v, w), ⟨by simpa using hv, by simpa using hw⟩, rfl⟩

/-- The bilinear square mass is nonnegative, including empty matrix labels. -/
theorem bilinearSquareMass_nonneg (D : ι → Matrix n n ℂ) (s : Finset ι) :
    0 ≤ bilinearSquareMass D s := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq D s
  rw [he]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

open scoped Matrix.Norms.L2Operator in
/-- The actual bilinear square energy has no dimension factor in its uniform
bound by the sum of squared named spectral norms. -/
theorem bilinearSquareMass_le_sum_specNorm_sq [DecidableEq n] (D : ι → Matrix n n ℂ) (s : Finset ι) :
    bilinearSquareMass D s ≤ ∑ i ∈ s, specNorm (D i) ^ 2 := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq D s
  rw [he]
  apply Finset.sum_le_sum
  intro i hi
  have hinner := norm_inner_le_norm (𝕜 := ℂ) v (WithLp.toLp 2 (D i *ᵥ w.ofLp))
  have hmv := (D i).l2_opNorm_mulVec w
  have heq : inner ℂ v (WithLp.toLp 2 (D i *ᵥ w.ofLp)) =
      star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp) := by
    rw [← WithLp.toLp_ofLp 2 v, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [heq] at hinner
  apply (sq_le_sq₀ (norm_nonneg _) (specNorm_nonneg _)).mpr
  calc _ ≤ ‖v‖ * ‖WithLp.toLp 2 (D i *ᵥ w.ofLp)‖ := hinner
    _ ≤ ‖v‖ * (specNorm (D i) * ‖w‖) :=
      mul_le_mul_of_nonneg_left hmv (norm_nonneg _)
    _ ≤ 1 * (specNorm (D i) * ‖w‖) :=
      mul_le_mul_of_nonneg_right hv (mul_nonneg (specNorm_nonneg _) (norm_nonneg _))
    _ ≤ specNorm (D i) := by
      simpa only [one_mul, mul_one] using
        mul_le_mul_of_nonneg_left hw (specNorm_nonneg (D i))

/-- Deleting summands decreases the actual supremum. -/
theorem bilinearSquareMass_mono (D : ι → Matrix n n ℂ) {s t : Finset ι} (hst : s ⊆ t) :
    bilinearSquareMass D s ≤ bilinearSquareMass D t := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq D s
  rw [he]
  apply le_trans _ (sum_bilinear_sq_le_bilinearSquareMass D t v w hv hw)
  exact Finset.sum_le_sum_of_subset_of_nonneg hst
    (fun _ _ _ => by positivity)

/-- At one actual maximizing probe, every deletion gap is bounded by that
probe's deleted square. The maximizer is constructed by compactness. -/
theorem exists_bilinearSquareMass_erase_gap_le [Fintype ι] [DecidableEq ι] (D : ι → Matrix n n ℂ) :
    ∃ v w : EuclideanSpace ℂ n, ‖v‖ ≤ 1 ∧ ‖w‖ ≤ 1 ∧
      bilinearSquareMass D Finset.univ = ∑ i, ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2 ∧
      ∀ i, bilinearSquareMass D Finset.univ - bilinearSquareMass D (Finset.univ.erase i) ≤
        ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2 := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq D Finset.univ
  refine ⟨v, w, hv, hw, by simpa using he, fun i => ?_⟩
  have h := sum_bilinear_sq_le_bilinearSquareMass D (Finset.univ.erase i) v w hv hw
  have hsum := Finset.sum_erase_add Finset.univ
    (fun j => ‖star v.ofLp ⬝ᵥ (D j *ᵥ w.ofLp)‖ ^ 2) (Finset.mem_univ i)
  linarith

/-- The bilinear square mass depends only on its selected coordinates. -/
theorem bilinearSquareMass_congr {D E : ι → Matrix n n ℂ} (s : Finset ι)
    (h : ∀ i ∈ s, D i = E i) : bilinearSquareMass D s = bilinearSquareMass E s := by
  unfold bilinearSquareMass
  apply congrArg sSup
  apply Set.image_congr
  intro p _
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

/-- The actual square energy of a difference is bounded by twice each
original energy, with no Hermitian or dimension assumption. -/
theorem bilinearSquareMass_sub_le (D E : ι → Matrix n n ℂ) (s : Finset ι) :
    bilinearSquareMass (fun i => D i - E i) s ≤
      2 * bilinearSquareMass D s + 2 * bilinearSquareMass E s := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq (fun i => D i - E i) s
  rw [he]
  have hpoint (i : ι) :
      ‖star v.ofLp ⬝ᵥ ((D i - E i) *ᵥ w.ofLp)‖ ^ 2 ≤
        2 * ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2 +
        2 * ‖star v.ofLp ⬝ᵥ (E i *ᵥ w.ofLp)‖ ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    have h := norm_sub_le (star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp))
      (star v.ofLp ⬝ᵥ (E i *ᵥ w.ofLp))
    nlinarith [norm_nonneg (star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp) -
      star v.ofLp ⬝ᵥ (E i *ᵥ w.ofLp)),
      norm_nonneg (star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)),
      norm_nonneg (star v.ofLp ⬝ᵥ (E i *ᵥ w.ofLp)),
      sq_nonneg (‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ -
        ‖star v.ofLp ⬝ᵥ (E i *ᵥ w.ofLp)‖)]
  calc
    _ ≤ ∑ i ∈ s, (2 * ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2 +
        2 * ‖star v.ofLp ⬝ᵥ (E i *ᵥ w.ofLp)‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 2 * (∑ i ∈ s, ‖star v.ofLp ⬝ᵥ (D i *ᵥ w.ofLp)‖ ^ 2) +
        2 * ∑ i ∈ s, ‖star v.ofLp ⬝ᵥ (E i *ᵥ w.ofLp)‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (sum_bilinear_sq_le_bilinearSquareMass D s v w hv hw) (by norm_num))
      (mul_le_mul_of_nonneg_left (sum_bilinear_sq_le_bilinearSquareMass E s v w hv hw) (by norm_num))

end NLAlib
