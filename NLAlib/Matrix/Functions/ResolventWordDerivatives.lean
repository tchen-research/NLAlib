import NLAlib.Matrix.Functions.ResolventCoordinateOperator
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import NLAlib.ForMathlib.Data.List.OfFn

/-!
# Ordered inverse-word derivatives in Hermitian real coordinates

A block is `(ζ,C)` and evaluates as `Rζ * C`.
Differentiating a block inserts `(ζ,Lh)` immediately before that block. Thus
one derivative adds exactly one resolvent block while preserving matrix order.
Three derivatives are indexed by `Fin m × Fin (m+1) × Fin (m+2)`.

The actual inverse derivative is reused from ResolventCoordinateOperator;
the noncommutative product rule is Mathlib's `HasFDerivAt.list_prod'`.

Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Lemma 6.9.
These are deterministic derivative prerequisites for the
`independent-sum-spectrum-universality` card; they do not establish
the probabilistic high-moment comparison.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator RightActions

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

/-- Ordered product of actual coordinate resolvents and fixed coefficients. -/
def hermitianCoordinateResolventWord {m : ℕ} (A : M)
    (w : Fin m → ℂ × M) (y : E) : M :=
  ((List.ofFn w).map (fun b => hermitianCoordinateResolvent A b.1 y * b.2)).prod

/-- Insert one actual derivative direction before the selected inverse block. -/
def resolventWordInsert {m : ℕ} (w : Fin m → ℂ × M) (i : Fin m) (H : M) :
    Fin (m + 1) → ℂ × M :=
  Fin.insertNth i.castSucc ((w i).1, H) w

omit [Fintype n] [DecidableEq n] in
/-- Nonreal shifts stay nonreal after the actual inverse insertion. -/
theorem im_ne_zero_resolventWordInsert {m : ℕ} (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) (i : Fin m) (H : M) :
    ∀ j, (resolventWordInsert w i H j).1.im ≠ 0 := by
  intro j
  refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
  · simpa only [resolventWordInsert, Fin.insertNth_apply_same] using hw i
  · simpa only [resolventWordInsert, Fin.insertNth_apply_succAbove] using hw k

/-- The primitive coordinate resolvent is genuinely smooth on the whole
real coordinate space; nonreal shifts are units at every reconstructed point. -/
theorem contDiff_hermitianCoordinateResolvent (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {r : WithTop ℕ∞} :
    ContDiff ℝ r (hermitianCoordinateResolvent A ζ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hu : IsUnit (ζ • (1 : M) - (A + L y)) :=
    (hA.add (isHermitian_hermitianMatrixFromRealCoordinates y)).isUnit_smul_one_sub_of_im_ne_zero hζ
  have hi := contDiffAt_ringInverse (n := r) ℝ hu.unit
  rw [hu.unit_spec] at hi
  have ha : ContDiffAt ℝ r (fun x : E => ζ • (1 : M) - (A + L x)) y :=
    contDiffAt_const.sub (contDiffAt_const.add (L).contDiff.contDiffAt)
  convert! hi.comp y ha using 1
  funext x
  simp [hermitianCoordinateResolvent, resolvent, Algebra.algebraMap_eq_smul_one]

/-- An actual ordered inverse word with fixed coefficients is globally smooth. -/
theorem contDiff_hermitianCoordinateResolventWord {m : ℕ} (A : M)
    (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) {r : WithTop ℕ∞} :
    ContDiff ℝ r (hermitianCoordinateResolventWord A w) := by
  induction m with
  | zero =>
    have heq : hermitianCoordinateResolventWord A w = fun _ : E => (1 : M) := by
      funext y
      simp [hermitianCoordinateResolventWord]
    rw [heq]
    exact contDiff_const
  | succ m ih =>
    have heq : hermitianCoordinateResolventWord A w = fun y =>
        (hermitianCoordinateResolvent A (w 0).1 y * (w 0).2) *
          hermitianCoordinateResolventWord A (Fin.tail w) y := by
      funext y
      simp only [hermitianCoordinateResolventWord, List.ofFn_succ, List.map_cons, List.prod_cons]
      rfl
    rw [heq]
    exact ((contDiff_hermitianCoordinateResolvent A hA (w 0).1 (hw 0)).mul
      contDiff_const).mul (ih (Fin.tail w) (fun i => hw i.succ))

private theorem hermitianCoordinateResolventWord_insert_eq {m : ℕ}
    (A : M) (w : Fin m → ℂ × M) (y : E) (i : Fin m) (H : M) :
    hermitianCoordinateResolventWord A (resolventWordInsert w i H) y =
      (((List.ofFn w).take i).map
        (fun b => hermitianCoordinateResolvent A b.1 y * b.2)).prod *
        (hermitianCoordinateResolvent A (w i).1 y * H *
          hermitianCoordinateResolvent A (w i).1 y * (w i).2) *
      (((List.ofFn w).drop (i + 1)).map
        (fun b => hermitianCoordinateResolvent A b.1 y * b.2)).prod := by
  unfold hermitianCoordinateResolventWord resolventWordInsert
  rw [List.ofFn_insertNth_eq_take_cons_drop]
  have hi : (i : ℕ) < (List.ofFn w).length := by simp
  simp only [Fin.val_castSucc]
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.map_append, List.map_cons, List.prod_append,
    List.prod_cons, List.getElem_ofFn, Fin.eta]
  simp only [mul_assoc]

/-- The real derivative of an actual inverse word is the sum of its genuine
ordered insertions. No derivative identity is assumed as a hypothesis. -/
theorem fderiv_hermitianCoordinateResolventWord_apply {m : ℕ}
    (A : M) (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) (y h : E) :
    fderiv ℝ (hermitianCoordinateResolventWord A w) y h =
      ∑ i : Fin m, hermitianCoordinateResolventWord A
        (resolventWordInsert w i (L h)) y := by
  let f : (ℂ × M) → E → M := fun b x => hermitianCoordinateResolvent A b.1 x * b.2
  let D : (ℂ × M) → E →L[ℝ] M := fun b =>
    ((ContinuousLinearMap.mul ℝ M).flip b.2).comp
      (hermitianCoordinateResolventDeriv A b.1 y)
  have hf (b : ℂ × M) (hb : b ∈ List.ofFn w) : HasFDerivAt (f b) (D b) y := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    simpa only [f, D, ContinuousLinearMap.flip_apply, Function.comp_def,
      ContinuousLinearMap.mul_apply'] using!
      ((ContinuousLinearMap.mul ℝ M).flip (w i).2).hasFDerivAt.comp y
        (hasFDerivAt_hermitianCoordinateResolvent A hA (w i).1 (hw i) y)
  have hp := HasFDerivAt.list_prod' hf
  change fderiv ℝ (fun x => ((List.ofFn w).map (fun b => f b x)).prod) y h = _
  rw [hp.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul, op_smul_eq_mul]
  refine Fintype.sum_equiv (finCongr (List.length_ofFn (f := w))) _ _ (fun i => ?_)
  rw [hermitianCoordinateResolventWord_insert_eq]
  simp only [D, Fin.getElem_fin, List.getElem_ofFn, finCongr_apply_coe,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
    hermitianCoordinateResolventDeriv_apply, mul_assoc]
  rfl

/-- The second actual derivative is the twice-inserted ordered word sum.
Directions are inserted from the inner derivative slot outwards. -/
theorem iteratedFDeriv_two_hermitianCoordinateResolventWord_apply {m : ℕ}
    (A : M) (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) (y : E) (h : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (hermitianCoordinateResolventWord A w) y h =
      ∑ i : Fin m, ∑ j : Fin (m + 1),
        hermitianCoordinateResolventWord A
          (resolventWordInsert (resolventWordInsert w i (L (h 1))) j (L (h 0))) y := by
  have hc := contDiff_hermitianCoordinateResolventWord A hA w hw (r := ⊤)
  have hh := hc.contDiffAt.differentiableAt_iteratedFDeriv (x := y) (m := 1) (by exact WithTop.coe_lt_top _)
  rw [hh.iteratedFDeriv_succ_apply_left' (m := h)]
  have heq : (fun x => iteratedFDeriv ℝ 1 (hermitianCoordinateResolventWord A w) x
      (Fin.tail h)) = fun x => ∑ i : Fin m,
        hermitianCoordinateResolventWord A (resolventWordInsert w i (L (h 1))) x := by
    funext x
    rw [iteratedFDeriv_one_apply, fderiv_hermitianCoordinateResolventWord_apply A hA w hw]
    rfl
  rw [heq]
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((contDiff_hermitianCoordinateResolventWord A hA _
      (im_ne_zero_resolventWordInsert w hw i (L (h 1))) (r := ⊤)).differentiable
        (by simp)).differentiableAt.hasFDerivAt (x := y))
  rw [hs.fderiv]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact fderiv_hermitianCoordinateResolventWord_apply A hA _
    (im_ne_zero_resolventWordInsert w hw i (L (h 1))) y (h 0)

/-- The third actual derivative is the genuine three-insertion ordered sum.
There are exactly `m(m+1)(m+2)` summands before any coincident words combine. -/
theorem iteratedFDeriv_three_hermitianCoordinateResolventWord_apply {m : ℕ}
    (A : M) (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) (y : E) (h : Fin 3 → E) :
    iteratedFDeriv ℝ 3 (hermitianCoordinateResolventWord A w) y h =
      ∑ i : Fin m, ∑ j : Fin (m + 1), ∑ k : Fin (m + 2),
        hermitianCoordinateResolventWord A
          (resolventWordInsert
            (resolventWordInsert (resolventWordInsert w i (L (h 2))) j (L (h 1)))
              k (L (h 0))) y := by
  have hc := contDiff_hermitianCoordinateResolventWord A hA w hw (r := ⊤)
  have hh := hc.contDiffAt.differentiableAt_iteratedFDeriv (x := y) (m := 2) (by exact WithTop.coe_lt_top _)
  rw [hh.iteratedFDeriv_succ_apply_left' (m := h)]
  have heq : (fun x => iteratedFDeriv ℝ 2 (hermitianCoordinateResolventWord A w) x
      (Fin.tail h)) = fun x => ∑ i : Fin m, ∑ j : Fin (m + 1),
        hermitianCoordinateResolventWord A
          (resolventWordInsert (resolventWordInsert w i (L (h 2))) j (L (h 1))) x := by
    funext x
    convert! iteratedFDeriv_two_hermitianCoordinateResolventWord_apply A hA w hw x
      (Fin.tail h) using 1
  rw [heq]
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((contDiff_hermitianCoordinateResolventWord A hA _
        (im_ne_zero_resolventWordInsert _
          (im_ne_zero_resolventWordInsert w hw i (L (h 2))) j (L (h 1)))
          (r := ⊤)).differentiable (by simp)).differentiableAt.hasFDerivAt (x := y)))
  rw [hs.fderiv]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact fderiv_hermitianCoordinateResolventWord_apply A hA _
    (im_ne_zero_resolventWordInsert _
      (im_ne_zero_resolventWordInsert w hw i (L (h 2))) j (L (h 1))) y (h 0)

/-- Exact combinatorial count of the native third-derivative insertion sum. -/
theorem card_third_resolvent_word_insertions (m : ℕ) :
    Fintype.card (Fin m × Fin (m + 1) × Fin (m + 2)) = m * (m + 1) * (m + 2) := by
  simp [Fintype.card_prod, mul_assoc]

/-- Any actual continuous real linear observation, including complex
normalized trace and its real part, preserves the exact ordered third
derivative formula. -/
theorem iteratedFDeriv_three_comp_hermitianCoordinateResolventWord_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    (T : M →L[ℝ] F) (A : M) (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) (y : E) (h : Fin 3 → E) :
    iteratedFDeriv ℝ 3 (fun x => T (hermitianCoordinateResolventWord A w x)) y h =
      ∑ i : Fin m, ∑ j : Fin (m + 1), ∑ k : Fin (m + 2),
        T (hermitianCoordinateResolventWord A
          (resolventWordInsert
            (resolventWordInsert (resolventWordInsert w i (L (h 2))) j (L (h 1)))
              k (L (h 0))) y) := by
  have hc := contDiff_hermitianCoordinateResolventWord A hA w hw (r := ⊤)
  change (iteratedFDeriv ℝ 3 (T ∘ hermitianCoordinateResolventWord A w) y) h = _
  rw [T.iteratedFDeriv_comp_left hc.contDiffAt (by simp)]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  rw [iteratedFDeriv_three_hermitianCoordinateResolventWord_apply A hA w hw]
  simp only [map_sum]

end NLAlib
