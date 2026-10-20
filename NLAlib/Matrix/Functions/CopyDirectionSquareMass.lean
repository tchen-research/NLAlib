import NLAlib.Matrix.Norms.ConvexSquareMass
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# One actual square-mass budget for three-copy interpolation directions

All bounds are deterministic and pointwise. A common convex ball of Hermitian
families retains both the operator radius and the realized aggregate square
mass. The affine shift is rewritten as convex combinations of copy differences,
so the reference copy is counted only once in the final common budget.
Source: the exact third-copy interpolation mechanism supporting
Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 6.9.
Supports independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

private def InSquareMassBall (r M : ℝ) (U : ι → Matrix n n ℂ) : Prop :=
  (∀ i, (U i).IsHermitian) ∧ (∀ i, specNorm (U i) ≤ r) ∧ specNorm (∑ i, U i ^ 2) ≤ M

open scoped Matrix.Norms.L2Operator in
private theorem inSquareMassBall_convex {r M t : ℝ} {U V : ι → Matrix n n ℂ}
    (hU : InSquareMassBall r M U) (hV : InSquareMassBall r M V)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    InSquareMassBall r M (fun i => (1 - t) • U i + t • V i) := by
  refine ⟨fun i => ((hU.1 i).smul (IsSelfAdjoint.all _)).add
    ((hV.1 i).smul (IsSelfAdjoint.all _)), ?_, ?_⟩
  · intro i
    calc
      _ ≤ ‖(1 - t) • U i‖ + ‖t • V i‖ := norm_add_le _ _
      _ = (1 - t) * specNorm (U i) + t * specNorm (V i) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
        rfl
      _ ≤ (1 - t) * r + t * r := add_le_add
        (mul_le_mul_of_nonneg_left (hU.2.1 i) (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left (hV.2.1 i) ht0)
      _ = r := by ring
  · calc
      _ ≤ (1 - t) * specNorm (∑ i, U i ^ 2) + t * specNorm (∑ i, V i ^ 2) :=
        specNorm_sum_one_sub_smul_add_smul_sq_le U V hU.1 hV.1 ht0 ht1
      _ ≤ (1 - t) * M + t * M := add_le_add
        (mul_le_mul_of_nonneg_left hU.2.2 (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left hV.2.2 ht0)
      _ = M := by ring

private theorem inSquareMassBall_zero {r M : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) :
    InSquareMassBall r M (fun _ : ι => (0 : Matrix n n ℂ)) := by
  refine ⟨fun _ => Matrix.isHermitian_zero, ?_, ?_⟩
  · intro i
    simpa only [specNorm_zero] using hr
  · simpa only [zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, specNorm_zero] using hM

open scoped Matrix.Norms.L2Operator in
private theorem inSquareMassBall_neg {r M : ℝ} {U : ι → Matrix n n ℂ}
    (hU : InSquareMassBall r M U) : InSquareMassBall r M (fun i => -U i) := by
  refine ⟨fun i => (hU.1 i).neg, ?_, ?_⟩
  · intro i
    simpa only [specNorm_eq_norm, norm_neg] using hU.2.1 i
  · simpa only [neg_sq] using hU.2.2

/-- The actual two interpolation directions and actual affine restoration
shift share radius 2R and square-mass budget twice the total realized mass of
three original Hermitian copies. Boundary parameters, zero radius and empty
matrix or family dimensions are included. -/
theorem norm_and_specNorm_sum_sq_copy_directions_le
    (Z : Fin 3 → ι → Matrix n n ℂ) (hHerm : ∀ s i, (Z s i).IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) (hZ : ∀ s i, specNorm (Z s i) ≤ R)
    {u v a : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    let M := 2 * (specNorm (∑ i, Z 0 i ^ 2) + specNorm (∑ i, Z 1 i ^ 2) +
      specNorm (∑ i, Z 2 i ^ 2))
    let D := fun i => Z 0 i - Z 1 i
    let E := fun i => (Z 1 i - Z 2 i) + u • (Z 0 i - Z 1 i)
    let H := fun i => a • ((1 - v) • Z 2 i + (v * (1 - u)) • Z 1 i +
      (u * v) • Z 0 i - Z 0 i)
    ((∀ i, (D i).IsHermitian) ∧ (∀ i, specNorm (D i) ≤ 2 * R) ∧ specNorm (∑ i, D i ^ 2) ≤ M) ∧
      ((∀ i, (E i).IsHermitian) ∧ (∀ i, specNorm (E i) ≤ 2 * R) ∧ specNorm (∑ i, E i ^ 2) ≤ M) ∧
      ((∀ i, (H i).IsHermitian) ∧ (∀ i, specNorm (H i) ≤ 2 * R) ∧ specNorm (∑ i, H i ^ 2) ≤ M) := by
  let M := 2 * (specNorm (∑ i, Z 0 i ^ 2) + specNorm (∑ i, Z 1 i ^ 2) +
    specNorm (∑ i, Z 2 i ^ 2))
  have hm (s : Fin 3) : 0 ≤ specNorm (∑ i, Z s i ^ 2) := specNorm_nonneg _
  have hM : 0 ≤ M := by dsimp only [M]; linarith [hm 0, hm 1, hm 2]
  have hdiff (s t : Fin 3)
      (hst : 2 * (specNorm (∑ i, Z s i ^ 2) + specNorm (∑ i, Z t i ^ 2)) ≤ M) :
      InSquareMassBall (2 * R) M (fun i => Z s i - Z t i) := by
    refine ⟨fun i => (hHerm s i).sub (hHerm t i), ?_, ?_⟩
    · intro i
      have h := (specNorm_sub_le (Z s i) (Z t i)).trans (add_le_add (hZ s i) (hZ t i))
      linarith
    · exact (specNorm_sum_sub_sq_le (Z s) (Z t) (hHerm s) (hHerm t)).trans hst
  have h01 := hdiff 0 1 (by dsimp only [M]; linarith [hm 2])
  have h12 := hdiff 1 2 (by dsimp only [M]; linarith [hm 0])
  have h02 := hdiff 0 2 (by dsimp only [M]; linarith [hm 1])
  have hZero := inSquareMassBall_zero (ι := ι) (n := n) (by linarith : 0 ≤ 2 * R) hM
  have hE := inSquareMassBall_convex h12 h02 hu0 hu1
  have hInner := inSquareMassBall_convex (inSquareMassBall_neg h01) hZero hu0 hu1
  have hOuter := inSquareMassBall_convex (inSquareMassBall_neg h02) hInner hv0 hv1
  have hH := inSquareMassBall_convex hZero hOuter ha0 ha1
  have hEeq : (fun i => (1 - u) • (Z 1 i - Z 2 i) + u • (Z 0 i - Z 2 i)) =
      (fun i => (Z 1 i - Z 2 i) + u • (Z 0 i - Z 1 i)) := by funext i; module
  have hHeq : (fun i => (1 - a) • (0 : Matrix n n ℂ) +
      a • ((1 - v) • (-(Z 0 i - Z 2 i)) + v •
        ((1 - u) • (-(Z 0 i - Z 1 i)) + u • (0 : Matrix n n ℂ)))) =
      (fun i => a • ((1 - v) • Z 2 i + (v * (1 - u)) • Z 1 i +
        (u * v) • Z 0 i - Z 0 i)) := by funext i; module
  rw [hEeq] at hE
  rw [hHeq] at hH
  exact ⟨h01, hE, hH⟩

end NLAlib
