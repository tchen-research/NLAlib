import NLAlib.Probability.Transforms.TensorChebyshevMomentWasserstein
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The two-dimensional reciprocal-square Chebyshev lattice sum

The two axes are bounded by the convergent square reciprocal series. Each
positive row is bounded by its elementary arctangent integral, leaving the
ordinary harmonic sum and its logarithmic upper bound.
-/

noncomputable section
open Real MeasureTheory Set Finset intervalIntegral
namespace NLAlib

/-- Number of retained tensor modes, with the exact constant mode removed. -/
theorem card_tensorChebyshevMomentIndices (d M : ℕ) :
    (tensorChebyshevMomentIndices d M).card = (M+1)^d-1 := by
  unfold tensorChebyshevMomentIndices
  rw [Finset.card_erase_of_mem (Fintype.mem_piFinset.mpr (fun _ => by simp)),Fintype.card_piFinset]
  simp

private theorem sum_range_add_one_inv_sq_add_sq_le (M : ℕ) {c : ℝ} (hc : 0 < c) :
    (∑ k ∈ range M, (c^2+((k+1 : ℕ) : ℝ)^2)⁻¹) ≤ π/(2*c) := by
  have ha : AntitoneOn (fun x : ℝ => (c^2+x^2)⁻¹) (Icc 0 (M : ℝ)) := by
    intro x hx y hy hxy
    apply inv_anti₀ (by positivity)
    nlinarith [hx.1,hy.1]
  have hi := AntitoneOn.sum_le_integral (f := fun x : ℝ => (c^2+x^2)⁻¹)
    (a := M) (x₀ := 0) (by simpa using ha)
  simp only [zero_add] at hi
  apply hi.trans
  rw [integral_inv_sq_add_sq hc.ne',zero_div,arctan_zero,sub_zero]
  have h := arctan_lt_pi_div_two ((M : ℝ)/c)
  have hmul := mul_le_mul_of_nonneg_left h.le (inv_nonneg.mpr hc.le)
  convert hmul using 1
  ring

private theorem sum_range_add_one_inv_sq_le (M : ℕ) :
    (∑ j ∈ range M, (((j+1 : ℕ) : ℝ)^2)⁻¹) ≤ π^2/6 := by
  have h := hasSum_zeta_two.summable.sum_le_tsum (range (M+1)) (fun _ _ => by positivity)
  rw [hasSum_zeta_two.tsum_eq,Finset.sum_range_succ'] at h
  simpa only [Nat.cast_zero,zero_pow (by norm_num : 2 ≠ 0),div_zero,zero_add,add_zero,one_div] using h

private theorem sum_tensor_lattice_eq_square (M : ℕ) :
    (∑ α ∈ tensorChebyshevMomentIndices 2 M,(tensorChebyshevIndexNormSq α)⁻¹) =
      ∑ j ∈ range (M+1),∑ k ∈ range (M+1),((j : ℝ)^2+(k : ℝ)^2)⁻¹ := by
  let s := Fintype.piFinset (fun _ : Fin 2 => range (M+1))
  have hzero : (0 : Fin 2 → ℕ) ∈ s := Fintype.mem_piFinset.mpr (fun _ => by simp)
  have herase := s.sum_erase_add (fun α => (tensorChebyshevIndexNormSq α)⁻¹) hzero
  have he : (∑ α ∈ tensorChebyshevMomentIndices 2 M,(tensorChebyshevIndexNormSq α)⁻¹) =
      ∑ α ∈ s,(tensorChebyshevIndexNormSq α)⁻¹ := by
    simpa only [tensorChebyshevMomentIndices,s,tensorChebyshevIndexNormSq,
      Pi.zero_apply,Nat.cast_zero,zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero,inv_zero,add_zero] using herase
  rw [he,← Finset.sum_product (f := fun p : ℕ × ℕ => ((p.1 : ℝ)^2+(p.2 : ℝ)^2)⁻¹)]
  apply Finset.sum_bij (fun α _ => (α 0,α 1))
  · intro α hα
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hα 0,Fintype.mem_piFinset.mp hα 1⟩
  · intro α hα β hβ hab
    funext i
    fin_cases i
    · exact congrArg Prod.fst hab
    · exact congrArg Prod.snd hab
  · intro p hp
    refine ⟨![p.1,p.2],?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      fin_cases i
      · exact (Finset.mem_product.mp hp).1
      · exact (Finset.mem_product.mp hp).2
    · simp
  · intro α _
    simp [tensorChebyshevIndexNormSq,Fin.sum_univ_two]

private theorem sum_square_inv_eq_axes_add_interior (M : ℕ) :
    (∑ j ∈ range (M+1),∑ k ∈ range (M+1),((j : ℝ)^2+(k : ℝ)^2)⁻¹) =
      2*(∑ j ∈ range M,(((j+1 : ℕ) : ℝ)^2)⁻¹) +
      ∑ j ∈ range M,∑ k ∈ range M,
        ((((j+1 : ℕ) : ℝ)^2+((k+1 : ℕ) : ℝ)^2))⁻¹ := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero,zero_pow (by norm_num : 2 ≠ 0),zero_add]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero,zero_pow (by norm_num : 2 ≠ 0),inv_zero]
  simp_rw [Finset.sum_range_succ',Nat.cast_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero]
  rw [Finset.sum_add_distrib]
  ring

/-- The explicit source lattice bound for every positive tensor degree. -/
theorem sum_inv_tensorChebyshevIndexNormSq_le {M : ℕ} (_hM : 1 ≤ M) :
    (∑ α ∈ tensorChebyshevMomentIndices 2 M,(tensorChebyshevIndexNormSq α)⁻¹) ≤
      5+(π/2)*log M := by
  rw [sum_tensor_lattice_eq_square,sum_square_inv_eq_axes_add_interior]
  have hrows : (∑ j ∈ range M,∑ k ∈ range M,
      ((((j+1 : ℕ) : ℝ)^2+((k+1 : ℕ) : ℝ)^2))⁻¹) ≤ (π/2)*(harmonic M : ℝ) := by
    calc
      _ ≤ ∑ j ∈ range M,π/(2*((j+1 : ℕ) : ℝ)) := Finset.sum_le_sum
        (fun j _ => sum_range_add_one_inv_sq_add_sq_le M (by positivity))
      _ = _ := by
        simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        push_cast
        field_simp
  have haxes := sum_range_add_one_inv_sq_le M
  have hh := harmonic_le_one_add_log M
  have hp : π^2/3+π/2 ≤ 5 := by nlinarith [pi_pos,pi_lt_d2]
  have hlog := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ π/2)
  nlinarith

/-- Uniform control of the actual normalized tensor moments gives the source's
explicit weighted moment error. -/
theorem tensorChebyshevMomentError_le_of_discrepancy_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) {M : ℕ} (hM : 1 ≤ M)
    {R : ℝ} (hR : 0 ≤ R)
    (hcoord : ∀ α ∈ tensorChebyshevMomentIndices 2 M,
      |tensorChebyshevMomentDiscrepancy μ ν α| ≤ R) :
    tensorChebyshevMomentError μ ν M ≤ R*sqrt (5+(π/2)*log M) := by
  have hL : 0 ≤ 5+(π/2)*log M := by
    have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hl := log_nonneg hm
    positivity
  have he : tensorChebyshevMomentError μ ν M ^ 2 ≤ R^2*(5+(π/2)*log M) := by
    rw [tensorChebyshevMomentError_sq]
    calc
      _ ≤ ∑ α ∈ tensorChebyshevMomentIndices 2 M,R^2*(tensorChebyshevIndexNormSq α)⁻¹ := by
        apply Finset.sum_le_sum
        intro α hα
        have hsq : tensorChebyshevMomentDiscrepancy μ ν α ^ 2 ≤ R^2 := by
          have h := (sq_le_sq₀ (abs_nonneg _) hR).mpr (hcoord α hα)
          simpa only [sq_abs] using h
        exact (div_le_div_of_nonneg_right hsq (by
          unfold tensorChebyshevIndexNormSq
          positivity)).trans_eq (by ring)
      _ = R^2*∑ α ∈ tensorChebyshevMomentIndices 2 M,(tensorChebyshevIndexNormSq α)⁻¹ :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_tensorChebyshevIndexNormSq_le hM) (sq_nonneg R)
  have hroot : (R*sqrt (5+(π/2)*log M))^2 = R^2*(5+(π/2)*log M) := by
    rw [mul_pow,sq_sqrt hL]
  have hnon : 0 ≤ tensorChebyshevMomentError μ ν M := sqrt_nonneg _
  have hright : 0 ≤ R*sqrt (5+(π/2)*log M) := mul_nonneg hR (sqrt_nonneg _)
  nlinarith

end NLAlib
