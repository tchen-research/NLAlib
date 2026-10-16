import NLAlib.Matrix.Functions.LoewnerPositivity
import NLAlib.Matrix.Basic.QuadForm
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Löwner's matrix monotonicity criterion

The necessity direction differentiates in the all-ones positive direction.
The converse applies the scalar mean-value theorem to every quadratic form
on an ordered matrix segment. Tropp (2022), Chapter 14.
-/

noncomputable section
open Matrix Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Evaluation of a fixed real quadratic form is a continuous real linear
functional of its matrix argument. -/
def reQuadFormCLM (x : n → ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun A := (quadForm A x).re
      map_add' A B := by simp [quadForm, Matrix.add_mulVec, dotProduct_add]
      map_smul' c A := by
        simp [quadForm, Matrix.smul_mulVec, dotProduct_smul] }

/-- Matrix monotonicity forces every finite Löwner matrix to be positive,
including lists with repeated nodes. -/
theorem OperatorMonotoneOn.posSemidef_loewnerMatrix {I : Set ℝ} {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn I f) (hI : IsOpen I) (hf : DifferentiableOn ℝ f I)
    (ev : n → ℝ) (hev : ∀ i, ev i ∈ I) : (loewnerMatrix f ev).PosSemidef := by
  let A := diagonal (fun i => (ev i : ℂ))
  have hA : A.IsHermitian := by
    change (diagonal (fun i => (ev i : ℂ))).IsHermitian
    exact isHermitian_diagonal_iff.mpr (fun i => by change star (ev i : ℂ) = _; simp)
  have hAI : spectrum ℝ A ⊆ I := by
    intro x hx
    have hx' : (x : ℂ) ∈ spectrum ℂ A := (spectrum.algebraMap_mem_iff ℂ).mpr hx
    rw [spectrum_diagonal] at hx'
    obtain ⟨i, hi⟩ := hx'
    exact Complex.ofReal_injective hi ▸ hev i
  let J : Matrix n n ℂ := Matrix.of fun _ _ => 1
  have hJ : J.PosSemidef := by
    simpa [J, vecMulVec] using posSemidef_vecMulVec_self_star (fun _ : n => (1 : ℂ))
  have h := hm.posSemidef_loewnerDerivative hI hf hA hAI ev 1
    (by simp [A]) hJ
  have hc : ((loewnerMatrix f ev).map Complex.ofReal).PosSemidef := by
    change ((1 : Matrix n n ℂ) * ((loewnerMatrix f ev).map Complex.ofReal ⊙
      ((1 : Matrix n n ℂ).conjTranspose * J * 1)) * (1 : Matrix n n ℂ).conjTranspose).PosSemidef at h
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
    have hj : (loewnerMatrix f ev).map Complex.ofReal ⊙ J =
        (loewnerMatrix f ev).map Complex.ofReal := by ext i j; simp [J]
    rwa [hj] at h
  exact (posSemidef_realMatrixComplexification_iff (loewnerMatrix f ev)).mp hc

/-- Positive Löwner matrices imply monotonicity on every ordered matrix
segment in an open convex scalar domain. -/
theorem cfc_le_of_posSemidef_loewnerMatrices {I : Set ℝ} {f : ℝ → ℝ}
    (hI : IsOpen I) (hcI : Convex ℝ I) (hf : DifferentiableOn ℝ f I)
    (hL : ∀ ev : n → ℝ, (∀ i, ev i ∈ I) → (loewnerMatrix f ev).PosSemidef)
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) (hAB : A ≤ B) :
    cfc f A ≤ cfc f B := by
  cases isEmpty_or_nonempty n with
  | inl he => exact (show cfc f A = cfc f B from Subsingleton.elim _ _).le
  | inr hn =>
    let D := B - A
    have hD : D.PosSemidef := Matrix.le_iff.mp hAB
    let C (t : ℝ) := A + t • D
    have hC (t : ℝ) : (C t).IsHermitian := hA.add (hD.isHermitian.smul (IsSelfAdjoint.all t))
    have hCI (t : ℝ) (ht : t ∈ Icc 0 1) : spectrum ℝ (C t) ⊆ I := by
      apply spectrum_subset_of_order_interval hcI hA hB (hC t) hAI hBI
      · rw [Matrix.le_iff, show C t - A = t • D by dsimp [C]; abel]
        exact hD.smul ht.1
      · rw [Matrix.le_iff, show B - C t = (1-t) • D by dsimp [C, D]; module]
        exact hD.smul (sub_nonneg.mpr ht.2)
    let L (t : ℝ) := loewnerDerivative f (hC t).eigenvalues (hC t).eigenvectorUnitary
    have hd (t : ℝ) (ht : t ∈ Icc 0 1) :
        HasDerivAt (fun s => cfc f (C s)) (L t D) t := by
      have hi (i : n) : (hC t).eigenvalues i ∈ I :=
        hCI t ht ((hC t).spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)
      have hfd := hasFDerivWithinAt_cfc_loewner (hC t)
        (fun i => (hf _ (hi i)).differentiableAt (hI.mem_nhds (hi i)))
        (hC t).eigenvalues (hC t).eigenvectorUnitary (hC t).spectral_theorem
      exact hfd.comp_hasDerivAt t (by simpa [C] using (((hasDerivAt_id t).smul_const D).const_add A))
        (Eventually.of_forall fun s => hC s)
    have hp (t : ℝ) (ht : t ∈ Icc 0 1) : (L t D).PosSemidef :=
      posSemidef_loewnerDerivative (hL _ fun i =>
        hCI t ht ((hC t).spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)) _ hD
    rw [Matrix.le_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
    have hdiff : (cfc f B - cfc f A).IsHermitian :=
      (show (cfc f B).IsHermitian from cfc_predicate _ _).sub (cfc_predicate _ _)
    refine ⟨hdiff, fun x => ?_⟩
    have hq (t : ℝ) (ht : t ∈ Icc 0 1) :=
      (reQuadFormCLM x).hasFDerivAt.comp_hasDerivAt t (hd t ht)
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
      (fun t ht => (hq t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hq t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hq t (interior_subset ht)).deriv]; exact (hp t (interior_subset ht)).re_quadForm_nonneg x)
    have hv := hm (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num) zero_le_one
    have hreal : 0 ≤ (quadForm (cfc f B - cfc f A) x).re := by
      simpa [reQuadFormCLM, C, D, quadForm, Matrix.sub_mulVec, dotProduct_sub] using sub_nonneg.mpr hv
    change 0 ≤ quadForm (cfc f B - cfc f A) x
    rw [← hdiff.ofReal_re_quadForm x]
    exact RCLike.ofReal_nonneg.mpr hreal

/-- Löwner's criterion in every finite size on an open interval:
operator monotonicity is equivalent to positivity of every finite
divided-difference matrix. Convex open sets include unbounded intervals.
atlas: matrix-monotone-loewner-criterion -/
theorem operatorMonotoneOn_iff_posSemidef_loewnerMatrix {I : Set ℝ} {f : ℝ → ℝ}
    (hI : IsOpen I) (hcI : Convex ℝ I) (hf : DifferentiableOn ℝ f I) :
    OperatorMonotoneOn I f ↔ ∀ (d : ℕ) (ev : Fin d → ℝ),
      (∀ i, ev i ∈ I) → (loewnerMatrix f ev).PosSemidef := by
  constructor
  · intro hm d ev hev
    exact hm.posSemidef_loewnerMatrix hI hf ev hev
  · intro hL d A B hA hB hAI hBI hAB
    exact cfc_le_of_posSemidef_loewnerMatrices hI hcI hf (hL d) hA hB hAI hBI hAB

end NLAlib
