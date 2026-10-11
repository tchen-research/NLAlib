/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyMarkedSites

set_option autoImplicit false

/-!
# Concrete heavy analysis operators

Literal one-site ladder matrices, external fibers, and heavy analysis actions.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- The lifted local heavy creation and annihilation matrices.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def rUpAt (r : Fin m) (i : Fin n) : FockOp m n :=
  siteKernel (r, i) rPromote

/-- The literal one-site heavy annihilation matrix acts on the finite pattern basis.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def rDownAt (r : Fin m) (i : Fin n) : FockOp m n :=
  siteKernel (r, i) rDemote

/-- The transpose of one-site heavy creation is one-site heavy annihilation.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem rUpAt_transpose (r : Fin m) (i : Fin n) :
    (rUpAt r i).transpose = rDownAt r i := by
  simp [rUpAt, rDownAt, transpose_siteKernel]

/-- The transpose of one-site heavy annihilation is one-site heavy creation.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem rDownAt_transpose (r : Fin m) (i : Fin n) :
    (rDownAt r i).transpose = rUpAt r i := by
  simp [rUpAt, rDownAt, transpose_siteKernel]

/-- The paper's heavy analysis leg `A_r`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def AUpMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun σ inp ↦ ∑ i, F.u i inp.1 * rUpAt r i σ inp.2

/-- The paper's adjoint heavy analysis leg `Ã_r`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def ADownMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun σ inp ↦ ∑ i, F.u i inp.1 * rDownAt r i σ inp.2

/-- The paper's heavy synthesis leg `B_r`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def BUpMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Fin d × Pattern m n) (Pattern m n) ℝ :=
  fun out τ ↦ ∑ i, F.u i out.1 * rUpAt r i out.2 τ

/-- External Euclidean fiber at one Fock pattern.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def fiber (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) : EVec d :=
  WithLp.toLp 2 (fun k ↦ x (k, p))

/-- A Euclidean external fiber reads the vector at its specified Fock pattern.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem fiber_apply (x : Fin d × Pattern m n → ℝ)
    (p : Pattern m n) (k : Fin d) : fiber x p k = x (k, p) := rfl

/-- One-site heavy creation has coefficient one precisely at the matching marked transition.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rUpAt_apply (r : Fin m) (i : Fin n) (out inp : Pattern m n) :
    rUpAt r i out inp =
      if out (r, i) = .two ∧ inp = setSite out (r, i) .one then 1 else 0 := by
  simpa [rUpAt, rPromote] using
    siteKernel_ketBra_apply (m := m) (n := n) (r, i) .two .one out inp

/-- One-site heavy annihilation has coefficient one precisely at the matching marked transition.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rDownAt_apply (r : Fin m) (i : Fin n) (out inp : Pattern m n) :
    rDownAt r i out inp =
      if out (r, i) = .one ∧ inp = setSite out (r, i) .two then 1 else 0 := by
  simpa [rDownAt, rDemote] using
    siteKernel_ketBra_apply (m := m) (n := n) (r, i) .one .two out inp

/-- Analyzing one heavy creation leg gives the frame coefficient of the transitioned external fiber.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem one_rUp_analysis (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (i : Fin n)
    (σ : Pattern m n) :
    (∑ inp : Fin d × Pattern m n,
        (F.u i inp.1 * rUpAt r i σ inp.2) * x inp) =
      if σ (r, i) = .two then
        analyze F (fiber x (setSite σ (r, i) .one)) i else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  by_cases hi : σ (r, i) = .two
  · simp only [rUpAt_apply, hi, true_and, if_true]
    simp only [analyze, fiber, PiLp.inner_apply, Real.inner_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp
  · simp [rUpAt_apply, hi]

/-- Analyzing one heavy annihilation leg gives the frame coefficient of the transitioned external fiber.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem one_rDown_analysis (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (i : Fin n)
    (σ : Pattern m n) :
    (∑ inp : Fin d × Pattern m n,
        (F.u i inp.1 * rDownAt r i σ inp.2) * x inp) =
      if σ (r, i) = .one then
        analyze F (fiber x (setSite σ (r, i) .two)) i else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  by_cases hi : σ (r, i) = .one
  · simp only [rDownAt_apply, hi, true_and, if_true]
    simp only [analyze, fiber, PiLp.inner_apply, Real.inner_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp
  · simp [rDownAt_apply, hi]

/-- A heavy creation analysis matrix acts by summing its admissible marked frame coefficients.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpMatrix_mulVec (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (σ : Pattern m n) :
    Matrix.mulVec (AUpMatrix F r) x σ =
      ∑ i ∈ σ.heavyInRow r,
        analyze F (fiber x (setSite σ (r, i) .one)) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, AUpMatrix]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [one_rUp_analysis]
  rw [Pattern.heavyInRow, Finset.sum_filter]

/-- A heavy annihilation analysis matrix acts by summing its admissible marked frame coefficients.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownMatrix_mulVec (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (σ : Pattern m n) :
    Matrix.mulVec (ADownMatrix F r) x σ =
      ∑ i ∈ σ.lightInRow r,
        analyze F (fiber x (setSite σ (r, i) .two)) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, ADownMatrix]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [one_rDown_analysis]
  rw [Pattern.lightInRow, Finset.sum_filter]

/-- Squared Euclidean energy on the scalar Fock-pattern space.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def fockNormSq (y : Pattern m n → ℝ) : ℝ := ∑ p, y p ^ 2

/-- Full coordinate energy equals the sum of external-fiber energies.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem full_normSq_eq_sum_fiber (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq x = ∑ p, ParsevalFrame.normSq (fiber x p) := by
  simp only [FiniteHilbert.normSq, ParsevalFrame.normSq, PiLp.inner_apply,
    Real.inner_apply, fiber]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The fiber of an exact-grade projection is retained precisely on that pattern grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem fiber_gradeProjection (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    fiber (Matrix.mulVec (gradeProjection (d := d) nu) x) p =
      if p.grade = nu then fiber x p else 0 := by
  ext k
  by_cases hp : p.grade = nu <;>
    simp [fiber, gradeProjection_mulVec, hp]

/-- On an exact grade, occupation-weighted energy is the grade times the projected energy.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem weighted_gradeProjection (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, (p.grade : ℝ) * ParsevalFrame.normSq
      (fiber (Matrix.mulVec (gradeProjection (d := d) nu) x) p)) =
      (nu : ℝ) * FiniteHilbert.normSq
        (Matrix.mulVec (gradeProjection (d := d) nu) x) := by
  rw [full_normSq_eq_sum_fiber]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [fiber_gradeProjection]
  by_cases hp : p.grade = nu
  · subst nu
    simp
  · simp [hp, ParsevalFrame.normSq]

end

end NLAlib.SparseFock.HeavyBandsConcrete
