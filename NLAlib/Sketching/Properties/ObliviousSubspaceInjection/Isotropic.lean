/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Basic.QuadraticFunctional
import NLAlib.ForMathlib.LinearAlgebra.Matrix.Mul
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import NLAlib.ForMathlib.MeasureTheory.MatrixEntriesIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Matrix.Order

/-!
# Isotropic sketch laws

Square-integrable entries and an identity second-moment Gram matrix are equivalent to
preserving every fixed vector's squared norm in expectation. The Frobenius counterpart follows
by summing columns. These law-level facts supply atlas `osi-def` and `osi-cross-residual-bound`.

Adapted to the native matrix and norm APIs from `NLA-lib/NLAlib`, commit
`6a845a2ec27f37c1a98118c107a06a13ce45273d`,
`Sketching/Properties/Isotropic.lean` (Apache-2.0).
-/

noncomputable section
open MeasureTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω 𝕜 k n : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  [Fintype k] [Fintype n] [DecidableEq n] {μ : Measure Ω}

open scoped Matrix.Norms.L2Operator in
private local instance : NormedSpace ℝ (Matrix n n 𝕜) where
  toModule := inferInstance
  norm_smul_le := by
    intro r A
    have he : r • A = (r : 𝕜) • A := by
      ext i j
      simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rw [he]
    simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using norm_smul_le (r : 𝕜) A

open scoped Matrix.Norms.L2Operator in
/-- An isotropic sketch has square-integrable entries and second-moment Gram matrix equal to
the identity. Camaño–Epperly–Meyer–Tropp (2025), Definition 1.2. Atlas: `osi-def`.
atlas: osi-def (partial) -/
structure IsIsotropicSketch (S : Ω → Matrix k n 𝕜) (μ : Measure Ω) : Prop where
  /-- Entrywise second moments are finite. -/
  memLp : ∀ i j, MemLp (fun ω => S ω i j) 2 μ
  /-- The expected Gram matrix is the identity. -/
  integral_conjTranspose_mul_self : ∫ ω, (S ω)ᴴ * S ω ∂μ = 1

open scoped Matrix.Norms.L2Operator in
private theorem integrable_sketch_gram {S : Ω → Matrix k n 𝕜}
    (hS : ∀ i j, MemLp (fun ω => S ω i j) 2 μ) :
    Integrable (fun ω => (S ω)ᴴ * S ω) μ := by
  refine Matrix.integrable_iff_entries.mpr fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact integrable_finsetSum _ fun c _ => (hS c i).star.integrable_mul (hS c j)

open scoped Matrix.Norms.L2Operator in
private theorem integral_norm_mulVec_sq_eq {S : Ω → Matrix k n 𝕜}
    (hS : ∀ i j, MemLp (fun ω => S ω i j) 2 μ) (x : n → 𝕜) :
    ∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ =
      RCLike.re (quadForm (∫ ω, (S ω)ᴴ * S ω ∂μ) x) := by
  have hi := integrable_sketch_gram hS
  have hq := (quadFormContinuousLinearMap x).integral_comp_comm hi
  have hqi := (quadFormContinuousLinearMap x).integrable_comp hi
  have he (ω : Ω) : ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 =
      RCLike.re (quadForm ((S ω)ᴴ * S ω) x) := by
    rw [quadForm_conjTranspose_mul_self, norm_toLp_sq_eq_re_star_dotProduct]
  simp only [quadFormContinuousLinearMap_apply] at hq hqi
  simp_rw [he]
  rw [integral_re hqi, hq]

omit [DecidableEq n] in
private theorem eq_of_isHermitian_of_quadForm_eq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, quadForm A x = quadForm B x) : A = B := by
  have hle {C D : Matrix n n 𝕜} (hC : C.IsHermitian) (hD : D.IsHermitian)
      (he : ∀ x, quadForm C x = quadForm D x) : C ≤ D := by
    rw [Matrix.le_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hD.sub hC, fun x => ?_⟩
    change 0 ≤ quadForm (D - C) x
    have hz : quadForm (D - C) x = 0 := by
      simp only [quadForm, Matrix.sub_mulVec, dotProduct_sub]
      exact sub_eq_zero.mpr (he x).symm
    rw [hz]
  exact le_antisymm (hle hA hB h) (hle hB hA fun x => (h x).symm)

open scoped Matrix.Norms.L2Operator in
/-- Isotropy is equivalent to preservation of every deterministic vector's squared norm in
expectation, together with finite entrywise second moments.
Camaño–Epperly–Meyer–Tropp (2025), Definition 1.2. Atlas: `osi-def`.
atlas: osi-def (partial) -/
theorem isIsotropicSketch_iff {S : Ω → Matrix k n 𝕜} :
    IsIsotropicSketch S μ ↔ (∀ i j, MemLp (fun ω => S ω i j) 2 μ) ∧
      ∀ x : n → 𝕜, ∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ =
        ‖WithLp.toLp 2 x‖ ^ 2 := by
  constructor
  · intro h
    refine ⟨h.memLp, fun x => ?_⟩
    rw [integral_norm_mulVec_sq_eq h.memLp, h.integral_conjTranspose_mul_self]
    simp only [quadForm, Matrix.one_mulVec, norm_toLp_sq_eq_re_star_dotProduct]
  · rintro ⟨hm, hv⟩
    refine ⟨hm, ?_⟩
    have hG := Matrix.isHermitian_integral (ae_of_all μ fun ω =>
      Matrix.isHermitian_conjTranspose_mul_self (S ω))
    refine eq_of_isHermitian_of_quadForm_eq hG Matrix.isHermitian_one fun x => ?_
    rw [← hG.ofReal_re_quadForm x, ← Matrix.isHermitian_one.ofReal_re_quadForm x]
    congr 1
    rw [← integral_norm_mulVec_sq_eq hm, hv]
    simp only [quadForm, Matrix.one_mulVec, norm_toLp_sq_eq_re_star_dotProduct]

namespace IsIsotropicSketch

variable {S : Ω → Matrix k n 𝕜}

/-- The squared norm of an isotropic sketch applied to a fixed vector is integrable. -/
theorem integrable_norm_mulVec_sq (h : IsIsotropicSketch S μ) (x : n → 𝕜) :
    Integrable (fun ω => ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2) μ := by
  simp only [EuclideanSpace.norm_sq_eq]
  refine integrable_finsetSum _ fun i _ => ?_
  have hi : MemLp (fun ω => (S ω *ᵥ x) i) 2 μ := by
    simp only [Matrix.mulVec, dotProduct]
    exact memLp_finsetSum _ fun j _ => (h.memLp i j).mul_const (x j)
  exact hi.integrable_norm_pow (by norm_num)

/-- Isotropic sketches preserve every deterministic vector's squared norm in expectation. -/
theorem integral_norm_mulVec_sq (h : IsIsotropicSketch S μ) (x : n → 𝕜) :
    ∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ = ‖WithLp.toLp 2 x‖ ^ 2 :=
  (isIsotropicSketch_iff.mp h).2 x

private theorem frobSq_eq_sum_norm_col {p : Type*} [Fintype p] (M : Matrix k p 𝕜) :
    frobSq M = ∑ j, ‖WithLp.toLp 2 (M.col j)‖ ^ 2 := by
  rw [frobSq_eq_sum_norm_sq, Finset.sum_comm]
  simp only [EuclideanSpace.norm_sq_eq, Matrix.col_apply]

/-- The squared Frobenius norm of an isotropic sketch times a fixed matrix is integrable. -/
theorem integrable_frobSq_mul (h : IsIsotropicSketch S μ) {p : Type*} [Fintype p] (M : Matrix n p 𝕜) :
    Integrable (fun ω => frobSq (S ω * M)) μ := by
  simp only [frobSq_eq_sum_norm_col, col_mul_eq_mulVec_col]
  exact integrable_finsetSum _ fun j _ => h.integrable_norm_mulVec_sq (M.col j)

/-- Isotropic sketches preserve the squared Frobenius norm of every fixed matrix in
expectation. Camaño–Epperly–Meyer–Tropp (2025), proof of Lemma 2.1.
Atlas: `osi-cross-residual-bound`. -/
theorem integral_frobSq_mul (h : IsIsotropicSketch S μ) {p : Type*} [Fintype p] (M : Matrix n p 𝕜) :
    ∫ ω, frobSq (S ω * M) ∂μ = frobSq M := by
  simp only [frobSq_eq_sum_norm_col, col_mul_eq_mulVec_col]
  rw [integral_finsetSum _ fun j _ => h.integrable_norm_mulVec_sq (M.col j)]
  exact Finset.sum_congr rfl fun j _ => h.integral_norm_mulVec_sq (M.col j)

end IsIsotropicSketch
end NLAlib
