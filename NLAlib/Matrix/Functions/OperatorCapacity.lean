import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Order
import NLAlib.Matrix.Functions.DeterminantRatio

/-!
# Operator capacity of a real-linear map on complex matrices

Given a real-linear endomorphism `T` of `Matrix n n ℂ`, its *operator capacity* is the
infimum of the real parts of the determinants of `T X` over normalized positive definite `X`
(`X.PosDef ∧ X.det = 1`).  For completely positive maps this is the capacity used in
operator scaling: Garg--Gurvits--Oliveira--Wigderson (2015), *Operator scaling: theory and
applications*, Definition 2.6 and Proposition 2.7
([arXiv:1511.03730](https://arxiv.org/abs/1511.03730)).
The defining infimum is exactly the normalized determinant-ratio infimum studied in
`NLAlib.Matrix.Functions.DeterminantRatio` (`detRatio_normalized_sInf_eq`), which we reuse
here, so no optimization algorithm is involved in the proofs below.

## Main results

* `operatorCapacity` — the definition (as `sInf` over the normalized determinant objective).
* `operatorCapacity_attainable_nonempty` — the objective set is nonempty (take `X = 1`).
* `operatorCapacity_attainable_bddBelow` — the objective set is bounded below by `0`
  under the positivity hypothesis `hT : ∀ X, X.PosSemidef → (T X).PosSemidef`.
* `operatorCapacity_nonneg` — `operatorCapacity T ≥ 0` under the same hypothesis.
* `operatorCapacity_eq_sInf_ratio` — the capacity equals the determinant-ratio infimum.
* `operatorCapacity_congruence_scaling` — the exact invertible congruence scaling law:
  if `B`, `C` are invertible and `S X = B * T (C * X * C†) * B†` pointwise, then
  `operatorCapacity S = ‖det B‖² * ‖det C‖² * operatorCapacity T`.
* `krausMap` — the finite Kraus form `X ↦ ∑ i, A i * X * (A i)†`
  (a real-linear map), with the positivity bridge `krausMap_posSemidef`.

The scaling identity only uses a nonempty objective set bounded below by zero; it does not
assume that the infimum is attained or that capacity is positive. The scalar factors are
squared complex moduli (`Complex.normSq`). Tensor multiplicativity is not proved here.

## Notes on the definition over empty index types

When `n` is empty, the unique matrix is positive definite vacuously and its determinant
in `ℂ` is `1`. Thus the objective set is `{1}` and the capacity is `1`.
The basic nonemptiness, boundedness, and nonnegativity statements include this case.
The determinant-ratio bridge and scaling theorem use the positive-dimension hypothesis
required by the determinant-root normalization lemma.
-/

open scoped ComplexOrder MatrixOrder ComplexConjugate
open Matrix

namespace NLAlib

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The operator capacity of a real-linear map `T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ`:
the infimum of `(T X).det.re` over positive definite `X` with determinant `1`.
The objective set is always nonempty. For maps preserving positive semidefiniteness,
it is bounded below by zero; `sInf` is otherwise the total real infimum operation. -/
def operatorCapacity (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) : ℝ :=
  sInf {d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re}

/-- The objective set of `operatorCapacity` is nonempty: `X = 1` is positive definite with
determinant `1`. -/
theorem operatorCapacity_attainable_nonempty (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    ({d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re}).Nonempty := by
  refine ⟨(T (1 : Matrix n n ℂ)).det.re, 1, Matrix.PosDef.one, Matrix.det_one, rfl⟩

/-- Under the positivity hypothesis `hT`, the objective set of `operatorCapacity` is bounded
below by `0`. -/
theorem operatorCapacity_attainable_bddBelow
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef) :
    BddBelow {d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re} := by
  refine ⟨0, ?_⟩
  rintro d ⟨X, hX, -, rfl⟩
  exact (Complex.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg (hT X hX.posSemidef))).1

/-- `operatorCapacity` is nonnegative under the positivity hypothesis `hT`. -/
theorem operatorCapacity_nonneg (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef) :
    0 ≤ operatorCapacity T := by
  unfold operatorCapacity
  exact le_csInf (operatorCapacity_attainable_nonempty T)
    (by
      rintro d ⟨X, hX, -, rfl⟩
      exact (Complex.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg (hT X hX.posSemidef))).1)

/-- The capacity is the infimum of the determinant-ratio objective
`(T X).det.re / X.det.re` over positive definite `X`.  This is the equality proved in
`NLAlib.detRatio_normalized_sInf_eq`. -/
theorem operatorCapacity_eq_sInf_ratio (hN : 0 < Fintype.card n)
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    operatorCapacity T = sInf {d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ d = (T X).det.re / X.det.re} := by
  unfold operatorCapacity
  exact detRatio_normalized_sInf_eq hN T

/-- Determinant of a matrix congruence: `det (U * X * U†) = det U * det X * star (det U)`. -/
private theorem det_congr_mul_conjTranspose (U X : Matrix n n ℂ) :
    (U * X * U.conjTranspose).det = det U * X.det * star (det U) := by
  calc
    (U * X * U.conjTranspose).det = det (U * X) * det (U.conjTranspose) := by
      rw [Matrix.det_mul]
    _ = det U * X.det * star (det U) := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose]

/-- The determinant of a congruence by `U` is `Complex.normSq (det U)` times the determinant
(the scalar `Complex.normSq (det U)` is real, coerced to `ℂ`). -/
private theorem det_congr_mul_conjTranspose_normSq (U X : Matrix n n ℂ) :
    (U * X * U.conjTranspose).det = (Complex.normSq (det U) : ℂ) * X.det := by
  rw [det_congr_mul_conjTranspose]
  have hns : (Complex.normSq (det U) : ℂ) = (starRingEnd ℂ) (det U) * det U :=
    Complex.normSq_eq_conj_mul_self
  rw [hns]
  simp_rw [Complex.star_def]
  ring

/-- Real part of the determinant of a congruence: `(U * X * U†).det.re = normSq (det U) * X.det.re`. -/
private theorem det_re_congr_mul_conjTranspose_normSq (U X : Matrix n n ℂ) :
    (U * X * U.conjTranspose).det.re = Complex.normSq (det U) * X.det.re := by
  rw [det_congr_mul_conjTranspose_normSq U X]
  exact Complex.re_ofReal_mul (Complex.normSq (det U)) X.det

/-- Under the pointwise congruence identity `S X = B * T (C * X * C†) * B†`, the real part
of the determinant of `S X` is `normSq (det B)` times that of `T (C * X * C†)`. -/
private theorem re_det_map_congr (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (B C : Matrix n n ℂ) (hS : ∀ X, S X = B * T (C * X * C.conjTranspose) * B.conjTranspose)
    (X : Matrix n n ℂ) :
    (S X).det.re = Complex.normSq (det B) * (T (C * X * C.conjTranspose)).det.re := by
  calc
    (S X).det.re = (B * T (C * X * C.conjTranspose) * B.conjTranspose).det.re := by
      rw [hS X]
    _ = (det B * (T (C * X * C.conjTranspose)).det * star (det B)).re := by
      congr 1
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    _ = ((Complex.normSq (det B) : ℂ) * (T (C * X * C.conjTranspose)).det).re := by
      congr 1
      have hns : (Complex.normSq (det B) : ℂ) = (starRingEnd ℂ) (det B) * det B :=
        Complex.normSq_eq_conj_mul_self
      rw [hns]
      simp_rw [Complex.star_def]
      ring
    _ = Complex.normSq (det B) * (T (C * X * C.conjTranspose)).det.re := by
      exact Complex.re_ofReal_mul (Complex.normSq (det B)) (T (C * X * C.conjTranspose)).det

/-- Normalized determinant-ratio identity for the forward congruence: for positive definite
`X`, writing `Y = C * X * C†`,

`(S X).det.re / X.det.re = normSq (det B) * normSq (det C) * ((T Y).det.re / Y.det.re)`.
-/
private theorem ratio_eq_scaled (B C X : Matrix n n ℂ)
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hC : IsUnit C)
    (hS : ∀ X, S X = B * T (C * X * C.conjTranspose) * B.conjTranspose)
    (hX : X.PosDef) :
    (S X).det.re / X.det.re =
      (Complex.normSq (det B) * Complex.normSq (det C)) *
        ((T (C * X * C.conjTranspose)).det.re / (C * X * C.conjTranspose).det.re) := by
  have hCdet_ne : det C ≠ 0 := (Matrix.isUnit_iff_isUnit_det C).mp hC |>.ne_zero
  have hCnsq_pos : 0 < Complex.normSq (det C) := Complex.normSq_pos.2 hCdet_ne
  have hCnsq_ne : Complex.normSq (det C) ≠ 0 := ne_of_gt hCnsq_pos
  have hXdet_re_pos : 0 < X.det.re := (Complex.pos_iff.mp hX.det_pos).1
  have hXdet_re_ne : X.det.re ≠ 0 := ne_of_gt hXdet_re_pos
  have hYdet := det_re_congr_mul_conjTranspose_normSq C X
  have hYdet_re_ne : (C * X * C.conjTranspose).det.re ≠ 0 := by
    rw [hYdet]
    exact ne_of_gt (mul_pos hCnsq_pos hXdet_re_pos)
  have hv : (S X).det.re = Complex.normSq (det B) * (T (C * X * C.conjTranspose)).det.re :=
    re_det_map_congr T S B C hS X
  calc
    (S X).det.re / X.det.re
        = (Complex.normSq (det B) * (T (C * X * C.conjTranspose)).det.re) / X.det.re := by
          rw [hv]
    _ = Complex.normSq (det B) * ((T (C * X * C.conjTranspose)).det.re / X.det.re) := by
          ring
    _ = Complex.normSq (det B) * (Complex.normSq (det C) *
          ((T (C * X * C.conjTranspose)).det.re / (C * X * C.conjTranspose).det.re)) := by
          rw [hYdet]
          have hfrac :
              (T (C * X * C.conjTranspose)).det.re / X.det.re =
                Complex.normSq (det C) *
                  ((T (C * X * C.conjTranspose)).det.re /
                    (Complex.normSq (det C) * X.det.re)) := by
            field_simp [hXdet_re_ne, hCnsq_ne]
          rw [hfrac]
    _ = (Complex.normSq (det B) * Complex.normSq (det C)) *
          ((T (C * X * C.conjTranspose)).det.re / (C * X * C.conjTranspose).det.re) := by
          ring

/-- Normalized determinant-ratio identity for the inverse congruence: for positive definite
`Y` and `X = C⁻¹ * Y * (C⁻¹)†`,

`normSq (det B) * normSq (det C) * ((T Y).det.re / Y.det.re) = (S X).det.re / X.det.re`.
-/
private theorem ratio_eq_scaled_preimage (B C Y : Matrix n n ℂ)
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hC : IsUnit C)
    (hS : ∀ X, S X = B * T (C * X * C.conjTranspose) * B.conjTranspose)
    (hY : Y.PosDef) :
    (Complex.normSq (det B) * Complex.normSq (det C)) * ((T Y).det.re / Y.det.re) =
      (S (C⁻¹ * Y * (C⁻¹).conjTranspose)).det.re /
        (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
  have hCdet_ne : det C ≠ 0 := (Matrix.isUnit_iff_isUnit_det C).mp hC |>.ne_zero
  have hCnsq_pos : 0 < Complex.normSq (det C) := Complex.normSq_pos.2 hCdet_ne
  have hCnsq_ne : Complex.normSq (det C) ≠ 0 := ne_of_gt hCnsq_pos
  have hCinv : IsUnit C⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hC
  have hX : (C⁻¹ * Y * (C⁻¹).conjTranspose).PosDef := by
    simpa [Matrix.star_eq_conjTranspose] using (hCinv.posDef_star_right_conjugate_iff).mpr hY
  have hXdet_re_pos : 0 < (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re :=
    (Complex.pos_iff.mp hX.det_pos).1
  have hXdet_re_ne : (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re ≠ 0 := ne_of_gt hXdet_re_pos
  have hCong : C * (C⁻¹ * Y * (C⁻¹).conjTranspose) * C.conjTranspose = Y := by
    have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC
    calc
      C * (C⁻¹ * Y * (C⁻¹).conjTranspose) * C.conjTranspose
          = (C * C⁻¹) * Y * ((C⁻¹).conjTranspose * C.conjTranspose) := by
            simp [Matrix.mul_assoc]
      _ = (C * C⁻¹) * Y * (C * C⁻¹).conjTranspose := by
            rw [← Matrix.conjTranspose_mul]
      _ = Y := by
            rw [Matrix.mul_nonsing_inv C hCdet]
            simp
  have hYdet : Y.det.re = Complex.normSq (det C) * (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
    calc
      Y.det.re = (C * (C⁻¹ * Y * (C⁻¹).conjTranspose) * C.conjTranspose).det.re := by
        conv_lhs => rw [← hCong]
      _ = Complex.normSq (det C) * (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re :=
        det_re_congr_mul_conjTranspose_normSq C (C⁻¹ * Y * (C⁻¹).conjTranspose)
  have hYdet_re_ne : Y.det.re ≠ 0 := by
    rw [hYdet]
    exact ne_of_gt (mul_pos hCnsq_pos hXdet_re_pos)
  have hv : (S (C⁻¹ * Y * (C⁻¹).conjTranspose)).det.re =
      Complex.normSq (det B) * (T Y).det.re := by
    rw [re_det_map_congr T S B C hS (C⁻¹ * Y * (C⁻¹).conjTranspose)]
    rw [hCong]
  calc
    (Complex.normSq (det B) * Complex.normSq (det C)) * ((T Y).det.re / Y.det.re)
        = Complex.normSq (det B) * (Complex.normSq (det C) * ((T Y).det.re / Y.det.re)) := by
          ring
    _ = Complex.normSq (det B) * ((T Y).det.re / (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re) := by
          have hfrac :
              Complex.normSq (det C) * ((T Y).det.re / Y.det.re) =
                (T Y).det.re / (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
            rw [hYdet]
            field_simp [hXdet_re_ne, hYdet_re_ne, hCnsq_ne]
          rw [hfrac]
    _ = (Complex.normSq (det B) * (T Y).det.re) / (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
          ring
    _ = (S (C⁻¹ * Y * (C⁻¹).conjTranspose)).det.re /
          (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
          rw [hv]

/-- The exact invertible congruence scaling law for operator capacity.

Let `T` and `S` be real-linear maps on `Matrix n n ℂ`, `B`, `C` invertible complex matrices,
and suppose `S` satisfies the pointwise congruence identity

`∀ X, S X = B * T (C * X * C†) * B†`.

Then `operatorCapacity S = ‖det B‖² * ‖det C‖² * operatorCapacity T`, where `‖z‖²` is
`Complex.normSq z = ‖z‖²`. The hypothesis `hT` (preservation of positive semidefinite
matrices) guarantees that the objective set is bounded below by zero. It is nonempty
because the identity matrix is admissible. No attainment, injectivity, or positive-capacity
assumption on `T` is needed, and the zero-capacity case is covered.
Source: Garg--Gurvits--Oliveira--Wigderson (2015), Proposition 2.7; this statement applies
to all positive real-linear maps, including the completely positive maps in that source.
atlas: operator-capacity-scaling-identities (partial) -/
theorem operatorCapacity_congruence_scaling (hN : 0 < Fintype.card n)
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (B C : Matrix n n ℂ) (hB : IsUnit B) (hC : IsUnit C)
    (hS : ∀ X, S X = B * T (C * X * C.conjTranspose) * B.conjTranspose) :
    operatorCapacity S = Complex.normSq (det B) * Complex.normSq (det C) * operatorCapacity T := by
  let A : Set ℝ := {d | ∃ X : Matrix n n ℂ, X.PosDef ∧ d = (T X).det.re / X.det.re}
  let A' : Set ℝ := {d | ∃ X : Matrix n n ℂ, X.PosDef ∧ d = (S X).det.re / X.det.re}
  let a : ℝ := Complex.normSq (det B) * Complex.normSq (det C)
  have hBdet_ne : det B ≠ 0 := (Matrix.isUnit_iff_isUnit_det B).mp hB |>.ne_zero
  have hCdet_ne : det C ≠ 0 := (Matrix.isUnit_iff_isUnit_det C).mp hC |>.ne_zero
  have ha_pos : 0 < a := by
    exact mul_pos (Complex.normSq_pos.2 hBdet_ne) (Complex.normSq_pos.2 hCdet_ne)
  let e : ℝ ≃o ℝ := OrderIso.mulLeft₀ a ha_pos
  have hTcap : operatorCapacity T = sInf A := by
    rw [operatorCapacity_eq_sInf_ratio hN T]
  have hScap : operatorCapacity S = sInf A' := by
    rw [operatorCapacity_eq_sInf_ratio hN S]
  have hAne : A.Nonempty := by
    refine ⟨((T (1 : Matrix n n ℂ)).det.re / ((1 : Matrix n n ℂ).det.re)),
      1, Matrix.PosDef.one, rfl⟩
  have hAbdd : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro d ⟨X, hX, rfl⟩
    exact div_nonneg
      ((Complex.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg (hT X hX.posSemidef))).1)
      ((Complex.pos_iff.mp hX.det_pos).1).le
  have hA'_eq : A' = e '' A := by
    ext d
    constructor
    · rintro ⟨X, hX, hd⟩
      refine ⟨(T (C * X * C.conjTranspose)).det.re / (C * X * C.conjTranspose).det.re,
          ⟨C * X * C.conjTranspose, ?_, rfl⟩, ?_⟩
      · simpa [Matrix.star_eq_conjTranspose] using (hC.posDef_star_right_conjugate_iff).mpr hX
      · dsimp [e]
        rw [hd]
        exact (ratio_eq_scaled B C X T S hC hS hX).symm
    · intro hmem
      rcases hmem with ⟨y, ⟨hy, hed⟩⟩
      rcases hy with ⟨Y, hY, rfl⟩
      let X : Matrix n n ℂ := C⁻¹ * Y * (C⁻¹).conjTranspose
      have hX : X.PosDef := by
        have hCinv : IsUnit C⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hC
        dsimp [X]
        simpa [Matrix.star_eq_conjTranspose] using (hCinv.posDef_star_right_conjugate_iff).mpr hY
      refine ⟨X, hX, ?_⟩
      rw [← hed]
      dsimp [e, X]
      exact ratio_eq_scaled_preimage B C Y T S hC hS hY
  have hes : e (sInf A) = sInf (e '' A) := e.map_csInf' hAne hAbdd
  calc
    operatorCapacity S = sInf A' := hScap
    _ = sInf (e '' A) := by rw [hA'_eq]
    _ = e (sInf A) := hes.symm
    _ = a * sInf A := by simp [e]
    _ = Complex.normSq (det B) * Complex.normSq (det C) * operatorCapacity T := by
      rw [← hTcap]
      try dsimp [a]
      try ring

/-- The finite Kraus form `X ↦ ∑ i, A i * X * (A i)†` for a family `A` of complex square
matrices, viewed as a real-linear endomorphism of `Matrix n n ℂ`.  This is the standard
finite-dimensional example of a completely positive map used in the operator scaling
literature. -/
def krausMap {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ where
  toFun X := ∑ i, A i * X * (A i).conjTranspose
  map_add' X Y := by
    ext i j
    simp [Finset.sum_add_distrib, Matrix.add_mul, Matrix.mul_add]
  map_smul' c X := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      simp)

omit [DecidableEq n] in
/-- Evaluation of `krausMap`. -/
theorem krausMap_apply {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    krausMap A X = ∑ i, A i * X * (A i).conjTranspose :=
  rfl

omit [DecidableEq n] in
/-- Positivity bridge for the finite Kraus form: if `X` is positive semidefinite, then so is
`krausMap A X`. -/
theorem krausMap_posSemidef {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (X : Matrix n n ℂ) (hX : X.PosSemidef) :
    (krausMap A X).PosSemidef := by
  rw [krausMap_apply]
  exact Matrix.posSemidef_sum Finset.univ (fun i _ => by
    simpa using (hX.conjTranspose_mul_mul_same (A i).conjTranspose))

/-- The operator capacity of a finite Kraus map is well-defined and nonnegative: the
positivity bridge `krausMap_posSemidef` supplies the hypothesis of `operatorCapacity_nonneg`.
-/
theorem operatorCapacity_krausMap_nonneg {ι : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) :
    0 ≤ operatorCapacity (krausMap A) := by
  exact operatorCapacity_nonneg (krausMap A) (krausMap_posSemidef A)

end

end NLAlib
