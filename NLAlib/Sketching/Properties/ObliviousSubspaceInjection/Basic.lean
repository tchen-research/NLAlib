/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Sketching.Properties.ObliviousSubspaceInjection.Isotropic
import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Matrix.Spectral.Core
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Measure.Real

/-!
# Oblivious subspace injections

The lower embedding event is quantified over each fixed deterministic frame. Isotropy is a
separate law property. The event need not be shared by every subspace. Camaño–Epperly–Meyer–Tropp
(2025), Definition 1.2 and Proposition 1.15. Atlas: `osi-def`.

The lower-embedding and law interfaces are adapted from `NLA-lib/NLAlib` commit
`6a845a2ec27f37c1a98118c107a06a13ce45273d`,
`Sketching/Properties/{SubspaceEmbedding,Oblivious}.lean` (Apache-2.0).
-/

noncomputable section
open MeasureTheory
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

variable {𝕜 k n r : Type*} [RCLike 𝕜] [Fintype k] [Fintype n] [Fintype r]

/-- The lower half of an embedding on the column space of `U`, without any upper bound.
Camaño–Epperly–Meyer–Tropp (2025), Definition 1.2. -/
def IsSubspaceInjection (S : Matrix k n 𝕜) (U : Matrix n r 𝕜) (α : ℝ) : Prop :=
  ∀ x : r → 𝕜, α * ‖WithLp.toLp 2 (U *ᵥ x)‖ ^ 2 ≤
    ‖WithLp.toLp 2 (S *ᵥ (U *ᵥ x))‖ ^ 2

private theorem norm_mulVec_sq_of_hasOrthonormalCols [DecidableEq r]
    {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) (x : r → 𝕜) :
    ‖WithLp.toLp 2 (Q *ᵥ x)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [norm_toLp_sq_eq_re_star_dotProduct,
    star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ,
    norm_toLp_sq_eq_re_star_dotProduct]

/-- A fixed frame's lower embedding event is closed as a set of sketch matrices. -/
theorem isClosed_setOf_isSubspaceInjection (U : Matrix n r 𝕜) (α : ℝ) :
    IsClosed {S : Matrix k n 𝕜 | IsSubspaceInjection S U α} := by
  simp only [IsSubspaceInjection, Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_le continuous_const
  simp only [EuclideanSpace.norm_sq_eq, Matrix.mulVec, dotProduct]
  fun_prop

/-- The lower event for an orthonormal frame is the lower Gram inequality.
atlas: osi-def (partial) -/
theorem HasOrthonormalCols.isSubspaceInjection_iff_gram [DecidableEq r]
    {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) (S : Matrix k n 𝕜) (α : ℝ) :
    IsSubspaceInjection S Q α ↔
      (α : 𝕜) • (1 : Matrix r r 𝕜) ≤ (S * Q)ᴴ * (S * Q) := by
  rw [Matrix.le_iff]
  let H := (S * Q)ᴴ * (S * Q) - (α : 𝕜) • (1 : Matrix r r 𝕜)
  have hH : H.IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self (S * Q)).sub
      (Matrix.isHermitian_one.smul (show IsSelfAdjoint (α : 𝕜) by simp [IsSelfAdjoint]))
  have he (x : r → 𝕜) : RCLike.re (quadForm H x) =
      ‖WithLp.toLp 2 ((S * Q) *ᵥ x)‖ ^ 2 - α * ‖WithLp.toLp 2 x‖ ^ 2 := by
    simp only [H, quadForm, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, map_sub, RCLike.re_ofReal_mul,
      norm_toLp_sq_eq_re_star_dotProduct]
    rw [← quadForm, quadForm_conjTranspose_mul_self]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨hH, fun x => ?_⟩
    change 0 ≤ quadForm H x
    rw [← hH.ofReal_re_quadForm x]
    apply RCLike.ofReal_nonneg.mpr
    rw [he, sub_nonneg]
    simpa only [Matrix.mulVec_mulVec, norm_mulVec_sq_of_hasOrthonormalCols hQ] using h x
  · rintro ⟨_, h⟩ x
    have hp : 0 ≤ RCLike.re (quadForm H x) := (RCLike.nonneg_iff.mp (h x)).1
    rw [he, sub_nonneg] at hp
    simpa only [Matrix.mulVec_mulVec, norm_mulVec_sq_of_hasOrthonormalCols hQ] using hp

/-- The fixed-frame lower event is exactly the smallest-singular-value inequality.
Camaño–Epperly–Meyer–Tropp (2025), Proposition 1.15. Atlas: `osi-def`.
atlas: osi-def (partial) -/
theorem HasOrthonormalCols.isSubspaceInjection_iff_le_singularValues_sq
    [DecidableEq r] [Nonempty r] {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    (S : Matrix k n 𝕜) {α : ℝ} (hα : 0 ≤ α) :
    IsSubspaceInjection S Q α ↔ α ≤ singularValues (S * Q) (Fintype.card r - 1) ^ 2 := by
  constructor
  · intro h
    have hs : Real.sqrt α ≤ singularValues (S * Q) (Fintype.card r - 1) := by
      apply le_singularValues_last
      intro x hx
      apply (Real.sqrt_le_iff).mpr
      refine ⟨norm_nonneg _, ?_⟩
      simpa only [Matrix.mulVec_mulVec, norm_mulVec_sq_of_hasOrthonormalCols hQ, hx,
        one_pow, mul_one] using h x
    have hp := pow_le_pow_left₀ (Real.sqrt_nonneg α) hs 2
    rwa [Real.sq_sqrt hα] at hp
  · intro h x
    have hv := singularValues_last_mul_norm_le (S * Q) x
    have hp := pow_le_pow_left₀
      (mul_nonneg (singularValues_nonneg _ _) (norm_nonneg _)) hv 2
    rw [mul_pow] at hp
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg ‖WithLp.toLp 2 x‖)
    simpa only [Matrix.mulVec_mulVec, norm_mulVec_sq_of_hasOrthonormalCols hQ]
      using hmul.trans hp

variable {Ω : Type*} [MeasurableSpace Ω] [DecidableEq n]

/-- An oblivious subspace injection is an isotropic measurable sketch law whose lower
embedding failure is at most `1/20` for every fixed `d`-frame. In the source test-matrix
orientation, apply this predicate to `fun ω => (Ω ω)ᴴ`.
Camaño–Epperly–Meyer–Tropp (2025), Definition 1.2. Atlas: `osi-def`.
atlas: osi-def (partial) -/
structure IsObliviousSubspaceInjection (S : Ω → Matrix k n 𝕜) (d : ℕ) (α : ℝ)
    (μ : Measure Ω) : Prop where
  /-- The sketch is a measurable matrix-valued random variable. -/
  measurable : Measurable S
  /-- Finite second moments and identity covariance. -/
  isotropic : IsIsotropicSketch S μ
  /-- The event is allowed to depend on the deterministic frame. -/
  injection : ∀ Q : Matrix n (Fin d) 𝕜, HasOrthonormalCols Q →
    μ.real {ω | ¬ IsSubspaceInjection (S ω) Q α} ≤ 1 / 20

omit [DecidableEq n] in
/-- The lower event for any fixed frame is measurable under a measurable sketch. -/
theorem measurableSet_isSubspaceInjection {S : Ω → Matrix k n 𝕜}
    (hS : Measurable S) (Q : Matrix n r 𝕜) (α : ℝ) :
    MeasurableSet {ω | IsSubspaceInjection (S ω) Q α} :=
  (isClosed_setOf_isSubspaceInjection Q α).measurableSet.preimage hS

/-- An OSI succeeds on each fixed deterministic frame with probability at least `19/20`.
The good event is per frame, rather than one event uniform in every frame.
Camaño–Epperly–Meyer–Tropp (2025), Definition 1.2. Atlas: `osi-def`.
atlas: osi-def (partial) -/
theorem IsObliviousSubspaceInjection.measureReal_isSubspaceInjection_ge
    {S : Ω → Matrix k n 𝕜} {d : ℕ} {α : ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h : IsObliviousSubspaceInjection S d α μ)
    (Q : Matrix n (Fin d) 𝕜) (hQ : HasOrthonormalCols Q) :
    19 / 20 ≤ μ.real {ω | IsSubspaceInjection (S ω) Q α} := by
  have hm := h.injection Q hQ
  have hc := measureReal_add_measureReal_compl (μ := μ)
    (measurableSet_isSubspaceInjection h.measurable Q α)
  rw [probReal_univ] at hc
  change μ.real {ω | IsSubspaceInjection (S ω) Q α} +
    μ.real {ω | ¬ IsSubspaceInjection (S ω) Q α} = 1 at hc
  linarith

end NLAlib
