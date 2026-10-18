import NLAlib.ForMathlib.Analysis.CStarAlgebra.AggregateProducts
import NLAlib.Matrix.Functions.HermitianResolvent
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Aggregate cubic resolvent words

Restoring a common Hermitian resolvent before summation retains the actual
squared sums of the endpoint directions and perturbations. Distinct endpoint
perturbations are allowed; the cubic specialization has the explicit constants
`R / eta^4` and `2 alpha^2 R^3 / eta^6`.

Source: Tatiana Brailovskaya and Ramon van Handel, *Universality and sharp
matrix concentration inequalities*, arXiv:2201.05142v3 (2024), §6.4, proof
of Lemma 6.11. These deterministic bounds support the atlas result
`matrix-resolvent-gaussian-universality`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
private theorem norm_sum_mul_mul_conjTranspose_le
    (G : M) (S Z U : ι → M) (α c R : ℝ)
    (hc : 0 ≤ c) (_hR : 0 ≤ R) (hG : ‖G‖ ≤ c)
    (hS : ∀ i, ‖S i‖ ≤ c) (hU : ∀ i, ‖U i‖ ≤ R)
    (heq : ∀ i, S i = G - α • (G * Z i * S i)) :
    ‖∑ i, (S i * U i) * (S i * U i)ᴴ‖ ≤
      2 * c ^ 2 * ‖∑ i, U i * (U i)ᴴ‖ +
        2 * α ^ 2 * R ^ 2 * c ^ 4 * ‖∑ i, Z i * (Z i)ᴴ‖ := by
  let X : M := ∑ i, U i * (U i)ᴴ
  let Y : M := ∑ i, Z i * (Z i)ᴴ
  let E : ι → M := fun i => S i * U i
  have hE (i : ι) : E i * (E i)ᴴ ≤ (c * R) ^ 2 • (1 : M) := by
    have hn : ‖E i‖ ≤ c * R := (norm_mul_le _ _).trans
      (mul_le_mul (hS i) (hU i) (norm_nonneg _) hc)
    have h := CStarAlgebra.mul_star_le_algebraMap_norm_sq (a := E i)
    refine h.trans ?_
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_le_smul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2)
        (show (0 : M) ≤ 1 from zero_le_one)
  have hterm (i : ι) :
      (E i) * (E i)ᴴ ≤
        (2 : ℝ) • (G * (U i * (U i)ᴴ) * Gᴴ) +
        (2 * α ^ 2 * (c * R) ^ 2) • (G * (Z i * (Z i)ᴴ) * Gᴴ) := by
    have he : E i = G * U i + (-α) • (G * Z i * E i) := by
      dsimp [E]
      nth_rw 1 [heq i]
      simp only [add_mul, neg_mul, smul_mul_assoc, sub_eq_add_neg, neg_smul, mul_assoc]
    have h := CStarAlgebra.add_mul_star_add_le (G * U i) ((-α) • (G * Z i * E i))
    rw [← he] at h
    change E i * (E i)ᴴ ≤ (2 : ℝ) • ((G * U i) * (G * U i)ᴴ) +
      (2 : ℝ) • (((-α) • (G * Z i * E i)) * ((-α) • (G * Z i * E i))ᴴ) at h
    have horder := star_right_conjugate_le_conjugate (hE i) (G * Z i)
    have hscaled := smul_le_smul_of_nonneg_left horder (show 0 ≤ 2 * α ^ 2 by positivity)
    have heq1 : (G * U i) * (G * U i)ᴴ = G * (U i * (U i)ᴴ) * Gᴴ := by
      simp only [Matrix.conjTranspose_mul, mul_assoc]
    have heq2 : (2 : ℝ) • (((-α) • (G * Z i * E i)) *
        ((-α) • (G * Z i * E i))ᴴ) =
        (2 * α ^ 2) • ((G * Z i) * (E i * (E i)ᴴ) * (G * Z i)ᴴ) := by
      simp only [Matrix.conjTranspose_smul, star_trivial,
        smul_mul_smul_comm, smul_smul, Matrix.conjTranspose_mul]
      congr 1 <;> noncomm_ring
    rw [heq1, heq2] at h
    refine h.trans (add_le_add le_rfl ?_)
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_assoc] using hscaled
  have hsum : (∑ i, E i * (E i)ᴴ) ≤
      (2 : ℝ) • (G * X * Gᴴ) +
        (2 * α ^ 2 * (c * R) ^ 2) • (G * Y * Gᴴ) := by
    convert Finset.sum_le_sum (fun i _ => hterm i) using 1
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum,
        ← Matrix.mul_sum, ← Matrix.sum_mul, X, Y]
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (Finset.sum_nonneg fun i _ => mul_star_self_nonneg (E i)) hsum
  have hsand (A : M) : ‖G * A * Gᴴ‖ ≤ c ^ 2 * ‖A‖ := by
    have h := (norm_mul_le (G * A) Gᴴ).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le G A) (norm_nonneg Gᴴ))
    rw [Matrix.l2_opNorm_conjTranspose] at h
    calc
      _ ≤ ‖G‖ * ‖A‖ * ‖G‖ := h
      _ = ‖G‖ ^ 2 * ‖A‖ := by ring
      _ ≤ c ^ 2 * ‖A‖ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg G) hG 2) (norm_nonneg A)
  calc
    _ ≤ ‖(2 : ℝ) • (G * X * Gᴴ) +
        (2 * α ^ 2 * (c * R) ^ 2) • (G * Y * Gᴴ)‖ := hnorm
    _ ≤ 2 * ‖G * X * Gᴴ‖ +
        (2 * α ^ 2 * (c * R) ^ 2) * ‖G * Y * Gᴴ‖ := by
      calc
        _ ≤ ‖(2 : ℝ) • (G * X * Gᴴ)‖ +
            ‖(2 * α ^ 2 * (c * R) ^ 2) • (G * Y * Gᴴ)‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul_of_nonneg (by positivity), norm_smul_of_nonneg (by positivity)]
    _ ≤ 2 * (c ^ 2 * ‖X‖) +
        (2 * α ^ 2 * (c * R) ^ 2) * (c ^ 2 * ‖Y‖) := by
      gcongr <;> exact hsand _
    _ = _ := by dsimp [X, Y]; ring

end NLAlib

namespace NLAlib
open scoped Matrix MatrixOrder ComplexOrder
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
local notation "M" => Matrix n n ℂ

/-- The first resolvent identity restores the common unperturbed resolvent
at the left end of a real Hermitian perturbation. -/
theorem resolvent_sub_smul_eq_sub_mul_resolvent (A Z : M) (α : ℝ) (ζ : ℂ)
    (hA : A.IsHermitian) (hZ : Z.IsHermitian) (hζ : ζ.im ≠ 0) :
    resolvent (A - α • Z) ζ = resolvent A ζ -
      α • (resolvent A ζ * Z * resolvent (A - α • Z) ζ) := by
  have hB := hA.sub (hZ.smul (isSelfAdjoint_iff.mpr (star_trivial α)))
  have h := Matrix.inv_sub_inv (A := ζ • (1 : M) - A)
    (B := ζ • (1 : M) - (A - α • Z))
    ⟨fun _ => hB.isUnit_smul_one_sub_of_im_ne_zero hζ,
      fun _ => hA.isUnit_smul_one_sub_of_im_ne_zero hζ⟩
  have he : (ζ • (1 : M) - (A - α • Z)) - (ζ • (1 : M) - A) = α • Z := by abel
  rw [he, Matrix.mul_smul, Matrix.smul_mul,
    ← resolvent_matrix_eq_inv, ← resolvent_matrix_eq_inv] at h
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm

/-- The first resolvent identity restores the common unperturbed resolvent
at the right end of a real Hermitian perturbation. -/
theorem resolvent_sub_smul_eq_sub_resolvent_mul (A Z : M) (α : ℝ) (ζ : ℂ)
    (hA : A.IsHermitian) (hZ : Z.IsHermitian) (hζ : ζ.im ≠ 0) :
    resolvent (A - α • Z) ζ = resolvent A ζ -
      α • (resolvent (A - α • Z) ζ * Z * resolvent A ζ) := by
  have hB := hA.sub (hZ.smul (isSelfAdjoint_iff.mpr (star_trivial α)))
  have h := Matrix.inv_sub_inv (A := ζ • (1 : M) - (A - α • Z))
    (B := ζ • (1 : M) - A)
    ⟨fun _ => hA.isUnit_smul_one_sub_of_im_ne_zero hζ,
      fun _ => hB.isUnit_smul_one_sub_of_im_ne_zero hζ⟩
  have he : (ζ • (1 : M) - A) - (ζ • (1 : M) - (A - α • Z)) = (-α) • Z := by
    simp only [neg_smul]
    abel
  rw [he, Matrix.mul_smul, Matrix.smul_mul,
    ← resolvent_matrix_eq_inv, ← resolvent_matrix_eq_inv, neg_smul] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (by abel)

open scoped Matrix.Norms.L2Operator in
/-- Aggregate resolvent words retain the squared sums of their two endpoint
directions and their two perturbation families. The endpoint resolvents may be
different single perturbations of the same Hermitian matrix; middle factors
only need a uniform spectral-norm bound. This is the deterministic estimate
underlying Tatiana Brailovskaya and Ramon van Handel, *Universality and sharp
matrix concentration inequalities*, arXiv:2201.05142v3 (2024), §6.4, proof of Lemma 6.11.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem specNorm_sum_resolvent_mul_mul_resolvent_le
    (A : M) (Z T U B W : ι → M) (α β R b : ℝ) (ζ : ℂ)
    (hA : A.IsHermitian) (hZ : ∀ i, (Z i).IsHermitian)
    (hT : ∀ i, (T i).IsHermitian) (hU : ∀ i, (U i).IsHermitian)
    (hW : ∀ i, (W i).IsHermitian) (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hUnorm : ∀ i, specNorm (U i) ≤ R) (hBnorm : ∀ i, specNorm (B i) ≤ b)
    (hWnorm : ∀ i, specNorm (W i) ≤ R) (hζ : ζ.im ≠ 0) :
    specNorm (∑ i, resolvent (A - α • Z i) ζ * U i * B i * W i *
      resolvent (A - β • T i) ζ) ≤
      b * |ζ.im|⁻¹ ^ 2 * (specNorm (∑ i, U i ^ 2) + specNorm (∑ i, W i ^ 2)) +
        b * R ^ 2 * |ζ.im|⁻¹ ^ 4 *
          (α ^ 2 * specNorm (∑ i, Z i ^ 2) + β ^ 2 * specNorm (∑ i, T i ^ 2)) := by
  let c : ℝ := |ζ.im|⁻¹
  let G : M := resolvent A ζ
  let S : ι → M := fun i => resolvent (A - α • Z i) ζ
  let Q : ι → M := fun i => resolvent (A - β • T i) ζ
  have hc : 0 ≤ c := inv_nonneg.mpr (abs_nonneg _)
  have hG : ‖G‖ ≤ c := hA.specNorm_resolvent_le hζ
  have hS (i : ι) : ‖S i‖ ≤ c :=
    (hA.sub ((hZ i).smul (isSelfAdjoint_iff.mpr (star_trivial α)))).specNorm_resolvent_le hζ
  have hQ (i : ι) : ‖Q i‖ ≤ c :=
    (hA.sub ((hT i).smul (isSelfAdjoint_iff.mpr (star_trivial β)))).specNorm_resolvent_le hζ
  have hleft := norm_sum_mul_mul_conjTranspose_le G S Z U α c R hc hR hG hS hUnorm
    (fun i => resolvent_sub_smul_eq_sub_mul_resolvent A (Z i) α ζ hA (hZ i) hζ)
  have hright := norm_sum_mul_mul_conjTranspose_le Gᴴ (fun i => (Q i)ᴴ) T W β c R
    hc hR (by simpa only [Matrix.l2_opNorm_conjTranspose] using hG)
    (fun i => by simpa only [Matrix.l2_opNorm_conjTranspose] using hQ i)
    hWnorm (fun i => by
      have h := congrArg Matrix.conjTranspose
        (resolvent_sub_smul_eq_sub_resolvent_mul A (T i) β ζ hA (hT i) hζ)
      simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
        Matrix.conjTranspose_mul, (hT i).eq, Matrix.mul_assoc] using h)
  have hsquares (F : ι → M) (hF : ∀ i, (F i).IsHermitian) :
      (∑ i, F i * (F i)ᴴ) = ∑ i, F i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hF i).eq, pow_two]
  rw [hsquares U hU, hsquares Z hZ] at hleft
  rw [hsquares W hW, hsquares T hT] at hright
  have hright' : ‖∑ i, (W i * Q i)ᴴ * (W i * Q i)‖ ≤
      2 * c ^ 2 * ‖∑ i, W i ^ 2‖ +
        2 * β ^ 2 * R ^ 2 * c ^ 4 * ‖∑ i, T i ^ 2‖ := by
    convert hright using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (hW i).eq, mul_assoc]
  have he : (∑ i, resolvent (A - α • Z i) ζ * U i * B i * W i *
      resolvent (A - β • T i) ζ) = ∑ i, (S i * U i) * B i * (W i * Q i) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [S, Q]
    noncomm_ring
  rw [he, specNorm_eq_norm]
  calc
    _ ≤ b / 2 * (‖∑ i, (S i * U i) * (S i * U i)ᴴ‖ +
        ‖∑ i, (W i * Q i)ᴴ * (W i * Q i)‖) :=
      CStarAlgebra.norm_sum_mul_mul_le (A := M) (ι := ι)
        (fun i => S i * U i) B (fun i => W i * Q i) hb hBnorm
    _ ≤ b / 2 * ((2 * c ^ 2 * ‖∑ i, U i ^ 2‖ +
        2 * α ^ 2 * R ^ 2 * c ^ 4 * ‖∑ i, Z i ^ 2‖) +
        (2 * c ^ 2 * ‖∑ i, W i ^ 2‖ +
        2 * β ^ 2 * R ^ 2 * c ^ 4 * ‖∑ i, T i ^ 2‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add hleft hright') (div_nonneg hb (by norm_num))
    _ = _ := by simp only [specNorm_eq_norm]; dsimp [c]; ring

open scoped Matrix.Norms.L2Operator in
/-- Cubic words in individually perturbed Hermitian resolvents obey a
strength-preserving aggregate squared-sum bound. There is no independence or
perturbation-smallness hypothesis, and the real perturbation coefficient is
arbitrary because its square is retained explicitly.
Source: Tatiana Brailovskaya and Ramon van Handel, *Universality and sharp
matrix concentration inequalities*, arXiv:2201.05142v3 (2024), §6.4, proof of Lemma 6.11.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem specNorm_sum_resolvent_cubic_word_le
    (A : M) (Z U V W : ι → M) (α R : ℝ) (ζ : ℂ)
    (hA : A.IsHermitian) (hZ : ∀ i, (Z i).IsHermitian)
    (hU : ∀ i, (U i).IsHermitian) (hW : ∀ i, (W i).IsHermitian)
    (hR : 0 ≤ R) (hUnorm : ∀ i, specNorm (U i) ≤ R)
    (hVnorm : ∀ i, specNorm (V i) ≤ R) (hWnorm : ∀ i, specNorm (W i) ≤ R)
    (hζ : 0 < ζ.im) :
    let S : ι → M := fun i => resolvent (A - α • Z i) ζ
    specNorm (∑ i, S i * U i * S i * V i * S i * W i * S i) ≤
      R / ζ.im ^ 4 * (specNorm (∑ i, U i ^ 2) + specNorm (∑ i, W i ^ 2)) +
        2 * α ^ 2 * R ^ 3 / ζ.im ^ 6 * specNorm (∑ i, Z i ^ 2) := by
  let S : ι → M := fun i => resolvent (A - α • Z i) ζ
  have hS (i : ι) : specNorm (S i) ≤ |ζ.im|⁻¹ :=
    (hA.sub ((hZ i).smul (isSelfAdjoint_iff.mpr (star_trivial α)))).specNorm_resolvent_le hζ.ne'
  have hb : ∀ i, specNorm (S i * V i * S i) ≤ R * |ζ.im|⁻¹ ^ 2 := by
    intro i
    calc
      _ ≤ (specNorm (S i) * specNorm (V i)) * specNorm (S i) :=
        (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (specNorm_mul_le _ _) (specNorm_nonneg _))
      _ ≤ (|ζ.im|⁻¹ * R) * |ζ.im|⁻¹ := by
        gcongr <;> first | exact specNorm_nonneg _ | exact hS i | exact hVnorm i
      _ = _ := by ring
  have h := specNorm_sum_resolvent_mul_mul_resolvent_le A Z Z U
    (fun i => S i * V i * S i) W α α R (R * |ζ.im|⁻¹ ^ 2) ζ
    hA hZ hZ hU hW hR (by positivity) hUnorm hb hWnorm hζ.ne'
  simp only [Matrix.mul_assoc, abs_of_pos hζ] at h ⊢
  refine h.trans_eq ?_
  simp only [div_eq_mul_inv, inv_pow]
  ring

end NLAlib
