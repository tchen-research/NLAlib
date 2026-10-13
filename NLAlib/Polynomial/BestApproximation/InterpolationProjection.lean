import NLAlib.Polynomial.BestApproximation.MinimaxError

/-!
# Lebesgue constants and near-best interpolation

Lagrange interpolation has operator norm exactly its Lebesgue constant. The extremizing
sample signs are realized by clipping their interpolating polynomial to `[-1,1]`.
Source: Trefethen, ATAP, Theorem 15.1.
Atlas: `lebesgue-constant-def`.
-/

noncomputable section

open Polynomial

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Lebesgue function is nonnegative. Source: ATAP, Chapter 15. -/
theorem lebesgueFunction_nonneg (v : ι → ℝ) (x : ℝ) : 0 ≤ lebesgueFunction v x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The partition of unity makes the Lebesgue function at least one everywhere.
Source: the Lagrange cardinal sum; helper for `lebesgue-constant-lower-bound`. -/
theorem one_le_lebesgueFunction [Nonempty ι] (v : ι → ℝ) (hv : Function.Injective v)
    (x : ℝ) : 1 ≤ lebesgueFunction v x := by
  have hsum := congrArg (fun p : ℝ[X] => p.eval x)
    (Lagrange.sum_basis hv.injOn (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty))
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_one] at hsum
  calc
    1 = |∑ j, (Lagrange.basis Finset.univ v j).eval x| := by rw [hsum]; norm_num
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _

/-- A pointwise nonnegative bound on the Lebesgue function bounds its canonical norm.
Source: the supremum norm definition; helper for `lebesgue-constant-lower-bound`. -/
theorem lebesgueConstant_le_of_forall {s : Set ℝ} [CompactSpace s] (v : ι → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ x ∈ s, lebesgueFunction v x ≤ L) :
    lebesgueConstant s v ≤ L := by
  unfold lebesgueConstant
  apply (ContinuousMap.norm_le _ hL).mpr
  intro x
  change |lebesgueFunction v (x : ℝ)| ≤ L
  rw [abs_of_nonneg (lebesgueFunction_nonneg _ _)]
  exact hbound x x.property

/-- The Lebesgue function is bounded by the Lebesgue constant on the compact domain.
Source: ATAP, Chapter 15. -/
theorem lebesgueFunction_le_lebesgueConstant {s : Set ℝ} [CompactSpace s]
    (v : ι → ℝ) {x : ℝ} (hx : x ∈ s) :
    lebesgueFunction v x ≤ lebesgueConstant s v := by
  let g : C(s, ℝ) := ⟨fun x : s => lebesgueFunction v x,
    by unfold lebesgueFunction; fun_prop⟩
  exact g.apply_le_norm ⟨x, hx⟩

/-- Evaluation of the interpolation map is the usual sum of cardinal polynomials.
Source: ATAP, Chapter 15. -/
theorem interpolationLinearMap_apply_eq_sum {s : Set ℝ} (v : ι → s)
    (f : C(s, ℝ)) (x : s) :
    interpolationLinearMap s v f x =
      ∑ i, f (v i) * (Lagrange.basis Finset.univ (fun i => (v i : ℝ)) i).eval (x : ℝ) := by
  simp [interpolationLinearMap_apply, Lagrange.interpolate_apply, eval_finsetSum]

/-- The cardinal-function sum bounds interpolation pointwise by a bound on its samples.
Source: Trefethen, ATAP, Theorem 15.1.
atlas: lebesgue-constant-def (partial) -/
theorem abs_interpolationLinearMap_apply_le {s : Set ℝ} (v : ι → s)
    (f : C(s, ℝ)) (x : s) (M : ℝ) (hM : ∀ i, |f (v i)| ≤ M) :
    |interpolationLinearMap s v f x| ≤ lebesgueFunction (fun i => (v i : ℝ)) x * M := by
  rw [interpolationLinearMap_apply_eq_sum]
  calc
    |∑ i, f (v i) * (Lagrange.basis Finset.univ (fun i => (v i : ℝ)) i).eval (x : ℝ)| ≤
        ∑ i, |f (v i) * (Lagrange.basis Finset.univ (fun i => (v i : ℝ)) i).eval (x : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(Lagrange.basis Finset.univ (fun i => (v i : ℝ)) i).eval (x : ℝ)| * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (hM i) (abs_nonneg _)
    _ = lebesgueFunction (fun i => (v i : ℝ)) x * M := by
      rw [lebesgueFunction, Finset.sum_mul]

/-- The Lebesgue constant bounds the norm of interpolation.
Source: Trefethen, ATAP, Theorem 15.1.
atlas: lebesgue-constant-def (partial) -/
theorem norm_interpolationLinearMap_le {s : Set ℝ} [CompactSpace s]
    (v : ι → s) (f : C(s, ℝ)) :
    ‖interpolationLinearMap s v f‖ ≤ lebesgueConstant s (fun i => (v i : ℝ)) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  rw [Real.norm_eq_abs]
  exact (abs_interpolationLinearMap_apply_le v f x ‖f‖
    (fun i => f.norm_coe_le_norm (v i))).trans
      (mul_le_mul_of_nonneg_right (lebesgueFunction_le_lebesgueConstant _ x.property)
        (norm_nonneg _))

/-- Lagrange interpolation as a bounded linear operator on continuous functions.
Source: Trefethen, ATAP, Chapter 15. -/
def interpolationOperator {s : Set ℝ} [CompactSpace s] (v : ι → s) :
    C(s, ℝ) →L[ℝ] C(s, ℝ) :=
  (interpolationLinearMap s v).mkContinuous
    (lebesgueConstant s (fun i => (v i : ℝ))) (norm_interpolationLinearMap_le v)

/-- The interpolation operator agrees with its algebraic linear map.
Source: Trefethen, ATAP, Chapter 15. -/
@[simp] theorem interpolationOperator_apply {s : Set ℝ} [CompactSpace s]
    (v : ι → s) (f : C(s, ℝ)) :
    interpolationOperator v f = interpolationLinearMap s v f := rfl

/-- Prescribed cardinal signs at a fixed point are attained by a continuous function of
norm at most one. Source: ATAP, proof of Theorem 15.1. The extension is obtained by
clipping the polynomial interpolating the signs, which is valid on any compact real set. -/
theorem exists_norm_le_one_interpolation_apply_eq_lebesgueFunction
    {s : Set ℝ} [CompactSpace s] (v : ι → s) (hv : Function.Injective v) (x : s) :
    ∃ f : C(s, ℝ), ‖f‖ ≤ 1 ∧
      interpolationLinearMap s v f x = lebesgueFunction (fun i => (v i : ℝ)) x := by
  let w : ι → ℝ := fun i => (v i : ℝ)
  have hw : Function.Injective w := fun i j h => hv (Subtype.ext h)
  let d : ι → ℝ := fun i => if (Lagrange.basis Finset.univ w i).eval (x : ℝ) < 0 then -1 else 1
  let p : ℝ[X] := Lagrange.interpolate Finset.univ w d
  let f : C(s, ℝ) := ⟨fun y => max (-1) (min 1 (p.eval y)), by fun_prop⟩
  have hd : ∀ i, d i = -1 ∨ d i = 1 := by
    intro i; dsimp [d]; split_ifs <;> simp
  have hnode : ∀ i, f (v i) = d i := by
    intro i
    have heval : p.eval (v i : ℝ) = d i :=
      Lagrange.eval_interpolate_at_node _ hw.injOn (Finset.mem_univ i)
    simp only [f, ContinuousMap.coe_mk, heval]
    rcases hd i with h | h <;> rw [h] <;> norm_num
  refine ⟨f, ?_, ?_⟩
  · apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro y
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · rw [interpolationLinearMap_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hnode]
    dsimp [d, w]
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (le_of_not_gt h), one_mul]

/-- The norm of interpolation is exactly its Lebesgue constant.
Source: Trefethen, ATAP, Theorem 15.1. -/
theorem norm_interpolationOperator_eq_lebesgueConstant {s : Set ℝ} [CompactSpace s]
    (v : ι → s) (hv : Function.Injective v) :
    ‖interpolationOperator v‖ = lebesgueConstant s (fun i => (v i : ℝ)) := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      (norm_interpolationLinearMap_le v)
  · let g : C(s, ℝ) := ⟨fun x : s => lebesgueFunction (fun i => (v i : ℝ)) x,
      by unfold lebesgueFunction; fun_prop⟩
    change ‖g‖ ≤ ‖interpolationOperator v‖
    apply (ContinuousMap.norm_le g (norm_nonneg (interpolationOperator v))).mpr
    intro x
    obtain ⟨f, hf, hfx⟩ := exists_norm_le_one_interpolation_apply_eq_lebesgueFunction v hv x
    change ‖lebesgueFunction (fun i => (v i : ℝ)) (x : ℝ)‖ ≤ ‖interpolationOperator v‖
    rw [Real.norm_eq_abs, abs_of_nonneg (lebesgueFunction_nonneg _ _)]
    calc
      lebesgueFunction (fun i => (v i : ℝ)) x = interpolationOperator v f x := hfx.symm
      _ ≤ ‖interpolationOperator v f‖ := (interpolationOperator v f).apply_le_norm x
      _ ≤ ‖interpolationOperator v‖ * ‖f‖ := (interpolationOperator v).le_opNorm f
      _ ≤ ‖interpolationOperator v‖ := by
        simpa using mul_le_mul_of_nonneg_left hf (norm_nonneg (interpolationOperator v))

/-- A nonempty interpolation grid has Lebesgue constant at least one.
Source: Trefethen, ATAP, Theorem 15.1. -/
theorem one_le_lebesgueConstant {s : Set ℝ} [CompactSpace s] [Nonempty ι]
    (v : ι → s) (hv : Function.Injective v) :
    1 ≤ lebesgueConstant s (fun i => (v i : ℝ)) := by
  let i := Classical.arbitrary ι
  have hw : Function.Injective (fun i => (v i : ℝ)) := fun i j h => hv (Subtype.ext h)
  have hsum := congrArg (fun p : ℝ[X] => p.eval (v i : ℝ))
    (Lagrange.sum_basis hw.injOn (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty))
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_one] at hsum
  calc
    1 = |∑ j, (Lagrange.basis Finset.univ (fun i => (v i : ℝ)) j).eval (v i : ℝ)| := by
      rw [hsum]; norm_num
    _ ≤ lebesgueFunction (fun i => (v i : ℝ)) (v i) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ lebesgueConstant s (fun i => (v i : ℝ)) :=
      lebesgueFunction_le_lebesgueConstant _ (v i).property

/-- Interpolation reproduces every polynomial of degree less than the number of nodes.
Source: Trefethen, ATAP, Chapter 15. -/
theorem interpolationLinearMap_eq_of_mem {s : Set ℝ} [Nonempty ι]
    (v : ι → s) (hv : Function.Injective v) {f : C(s, ℝ)}
    (hf : f ∈ polynomialApproximationSpace s (Fintype.card ι - 1)) :
    interpolationLinearMap s v f = f := by
  obtain ⟨p, hp, rfl⟩ := mem_polynomialApproximationSpace_iff.mp hf
  have hw : Function.Injective (fun i => (v i : ℝ)) := fun i j h => hv (Subtype.ext h)
  rw [interpolationLinearMap_apply]
  congr 1
  apply (Lagrange.eq_interpolate hw.injOn ?_).symm
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  exact hp.trans_lt (by simp only [Finset.card_univ]; exact_mod_cast Nat.pred_lt hcard.ne')

/-- Interpolation is within `1+Λ` of best degree-bounded uniform approximation.
Source: Trefethen, ATAP, Theorem 15.1.
atlas: lebesgue-constant-def -/
theorem norm_sub_interpolationLinearMap_le_minimaxError {s : Set ℝ} [CompactSpace s]
    [Nonempty ι] (v : ι → s) (hv : Function.Injective v) (f : C(s, ℝ)) :
    ‖f - interpolationLinearMap s v f‖ ≤
      (1 + lebesgueConstant s (fun i => (v i : ℝ))) * minimaxError (Fintype.card ι - 1) f :=
  norm_sub_projection_le_minimaxError _ _ _
    (fun _ hp => interpolationLinearMap_eq_of_mem v hv hp)
    (norm_interpolationLinearMap_le v) f

end NLAlib
