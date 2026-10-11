/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.FiniteHilbert
import NLAlib.Sketching.SparseFock.ParsevalFrame
import NLAlib.Sketching.SparseFock.LightSectorAbstract
import NLAlib.Sketching.SparseFock.MatrixTail
import Mathlib.Tactic

/-!
# Creation, annihilation, and one-particle shared-leg operators

Partition of the literal shared-leg proof from sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`.
The original `LightSectorConcrete` import re-exports this unchanged namespace.
Supports the `sparse-ose` moment proof.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace NLAlib.SparseFock.LightSectorConcrete
open ParsevalFrame LocalOperator FiniteOperator ExternalOperator FiniteHilbert
variable {d m n ell : ℕ}

/-- The annihilation operator `P_(r,i)` on the literal pattern basis.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def pAt (r : Fin m) (i : Fin n) : FockOp m n :=
  siteKernel (r, i) pDestroy

/-- The creation operator `P†_(r,i)` on the literal pattern basis.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def pDagAt (r : Fin m) (i : Fin n) : FockOp m n :=
  siteKernel (r, i) pCreate

/-- The rectangular matrix `C_r = Σ_i u_i ⊗ P†_(r,i)`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def CMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Fin d × Pattern m n) (Pattern m n) ℝ :=
  fun out inp ↦ ∑ i, F.u i out.1 * pDagAt r i out.2 inp

/-- The concrete positive shared-leg operator `G-hat = Σ_r C_r C_rᵀ`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def ghat (F : Frame n d) : FullOp d m n :=
  ∑ r, CMatrix F r * (CMatrix F r).transpose

/-- The transposed creation matrix has the corresponding annihilation entry formula.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem CMatrix_transpose_apply (F : Frame n d) (r : Fin m)
    (p : Pattern m n) (out : Fin d × Pattern m n) :
    (CMatrix F r).transpose p out =
      ∑ i, F.u i out.1 * pAt r i p out.2 := by
  simp only [Matrix.transpose_apply, CMatrix, pAt, pDagAt]
  apply Finset.sum_congr rfl
  intro i _hi
  have h := congrFun (congrFun (transpose_siteKernel (r, i) pCreate) p) out.2
  simp only [Matrix.transpose_apply, transpose_pCreate] at h
  rw [h]

/-- Entrywise expansion of `G-hat` as the displayed `Σ U_ij ⊗ P†_i P_j`.
The same-site terms are retained; no hollow-pair convention is used here.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ghat_apply (F : Frame n d)
    (out inp : Fin d × Pattern m n) :
    ghat (m := m) F out inp =
      ∑ r, ∑ i, ∑ j,
        (F.u i out.1 * F.u j inp.1) *
          (pDagAt r i * pAt r j) out.2 inp.2 := by
  classical
  simp only [ghat, Matrix.sum_apply, Matrix.mul_apply, CMatrix,
    CMatrix_transpose_apply]
  apply Finset.sum_congr rfl
  intro r _hr
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [pDagAt, pAt]
  apply Finset.sum_congr rfl
  intro mid _hmid
  ring

/-- The shared-leg operator is symmetric.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem ghat_transpose (F : Frame n d) :
    (ghat (m := m) F).transpose = ghat F := by
  rw [ghat]
  simp only [Matrix.transpose_sum, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- A pattern lies in the block with fixed heavy set `T` and exactly `ell`
light sites.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def InBlock (T : Finset (Site m n)) (ell : ℕ) (p : Pattern m n) : Prop :=
  p.heavy = T ∧ p.light.card = ell

/-- Membership in a fixed-heavy, fixed-light pattern block is decidable.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
instance instDecidableInBlock (T : Finset (Site m n)) (ell : ℕ)
    (p : Pattern m n) : Decidable (InBlock T ell p) := by
  unfold InBlock
  infer_instance

/-- The literal diagonal projection onto a fixed-heavy/fixed-light block.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def blockProjection (T : Finset (Site m n)) (ell : ℕ) : FullOp d m n :=
  by
    classical
    exact Matrix.diagonal fun x ↦ if InBlock T ell x.2 then 1 else 0

/-- The block projection is the diagonal indicator of block membership.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem blockProjection_apply (T : Finset (Site m n)) (ell : ℕ)
    (out inp : Fin d × Pattern m n) :
    blockProjection (d := d) T ell out inp =
      if out = inp ∧ InBlock T ell out.2 then 1 else 0 := by
  classical
  by_cases h : out = inp
  · subst inp
    by_cases hb : InBlock T ell out.2 <;>
      simp [blockProjection, Matrix.diagonal, hb]
  · simp [blockProjection, Matrix.diagonal, h]

/-- The pattern block projection is symmetric.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem blockProjection_transpose (T : Finset (Site m n)) (ell : ℕ) :
    (blockProjection (d := d) T ell).transpose = blockProjection T ell := by
  ext out inp
  simp only [Matrix.transpose_apply, blockProjection_apply]
  by_cases h : out = inp
  · subst inp
    simp
  · simp [h, Ne.symm h]

/-- The pattern block projection is idempotent.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem blockProjection_mul_self (T : Finset (Site m n)) (ell : ℕ) :
    blockProjection (d := d) T ell * blockProjection T ell =
      blockProjection T ell := by
  classical
  simp [blockProjection, Matrix.diagonal_mul_diagonal]

/-- Coordinate energy on the actual external-pattern Euclidean space.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def energy (x : Fin d × Pattern m n → ℝ) : ℝ :=
  ∑ a, x a ^ 2

/-- Quadratic form of a literal full matrix.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def quadratic (A : FullOp d m n) (x : Fin d × Pattern m n → ℝ) : ℝ :=
  ∑ a, x a * A.mulVec x a

/-- The column-space Gram matrix `U Uᵀ` on the `n` column coordinates.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def columnGram (F : Frame n d) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ inner ℝ (F.u i) (F.u j)

/-- Application of the column Gram matrix, kept as an explicit finite sum.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def columnGramApply (F : Frame n d) (x : EVec n) : EVec n :=
  WithLp.toLp 2 fun i ↦ ∑ j, columnGram F i j * x j

/-- Applying the column Gram operator is its matrix-vector product.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem columnGramApply_apply (F : Frame n d) (x : EVec n) (i : Fin n) :
    columnGramApply F x i = ∑ j, columnGram F i j * x j := rfl

/-- `U Uᵀ` is analysis after synthesis.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem columnGramApply_eq_analyze_synthesize (F : Frame n d) (x : EVec n)
    (i : Fin n) :
    columnGramApply F x i =
      analyze F (synthesize F Finset.univ (fun j ↦ x j)) i := by
  simp only [columnGramApply_apply, columnGram, analyze, synthesize,
    PiLp.inner_apply, Real.inner_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The cross-map column register `U Uᵀ` is an actual Euclidean contraction.
This proves, rather than assumes, the analytic input `‖P_(l←k)‖ ≤ 1`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem columnGram_energy_le (F : Frame n d) (x : EVec n) :
    ParsevalFrame.normSq (columnGramApply F x) ≤
      ParsevalFrame.normSq x := by
  let y : EVec d := synthesize F Finset.univ (fun j ↦ x j)
  have hanalysis : ParsevalFrame.normSq (columnGramApply F x) =
      ∑ i, (analyze F y i) ^ 2 := by
    simp only [ParsevalFrame.normSq, PiLp.inner_apply, Real.inner_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [columnGramApply_eq_analyze_synthesize]
    simp [y, pow_two]
  calc
    ParsevalFrame.normSq (columnGramApply F x) =
        ∑ i, (analyze F y i) ^ 2 := hanalysis
    _ = ParsevalFrame.normSq y := analysis_energy_eq F y
    _ ≤ ∑ j ∈ Finset.univ, |x j| ^ 2 := subset_synthesis F Finset.univ (fun j ↦ x j)
    _ = ParsevalFrame.normSq x := by
      rw [ParsevalFrame.normSq_eq_norm_sq, EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs]

/-- Quadratic two-vector form of the concrete cross-map contraction.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem two_columnGram_pairing_le (F : Frame n d) (x y : EVec n) :
    2 * inner ℝ (columnGramApply F x) y ≤
      ParsevalFrame.normSq x + ParsevalFrame.normSq y := by
  have hcs : inner ℝ (columnGramApply F x) y ≤
      ‖columnGramApply F x‖ * ‖y‖ := real_inner_le_norm _ _
  have hcontractSq := columnGram_energy_le F x
  rw [ParsevalFrame.normSq_eq_norm_sq,
    ParsevalFrame.normSq_eq_norm_sq] at hcontractSq ⊢
  have hcontract : ‖columnGramApply F x‖ ≤ ‖x‖ := by
    nlinarith [norm_nonneg (columnGramApply F x), norm_nonneg x]
  have hmul : ‖columnGramApply F x‖ * ‖y‖ ≤ ‖x‖ * ‖y‖ :=
    mul_le_mul_of_nonneg_right hcontract (norm_nonneg y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-! ## The labelled one-particle shared leg -/

/-- Coordinate form of trace Parseval.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_frame_coordinate_sq_eq_dim (F : Frame n d) :
    (∑ a, ∑ i, F.u i a * F.u i a) = (d : ℝ) := by
  have hdiag (a : Fin d) : ∑ i, F.u i a * F.u i a = 1 := by
    have h := congrFun (congrFun F.parseval a) a
    simpa [Matrix.sum_apply, ParsevalFrame.outer] using h
  simp_rw [hdiag]
  simp

/-- Trace Parseval: the total squared length of all frame rows is exactly `d`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_frame_normSq_eq_dim (F : Frame n d) :
    (∑ i, ParsevalFrame.normSq (F.u i)) = (d : ℝ) := by
  calc
    (∑ i, ParsevalFrame.normSq (F.u i)) =
        ∑ i, ∑ a, F.u i a * F.u i a := by
      simp only [ParsevalFrame.normSq, PiLp.inner_apply, Real.inner_apply]
    _ = ∑ a, ∑ i, F.u i a * F.u i a := Finset.sum_comm
    _ = (d : ℝ) := sum_frame_coordinate_sq_eq_dim F

/-- One shared vector `w_r = Σ_i u_i ⊗ e_r ⊗ e_i`, in literal
finite Euclidean coordinates.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def sharedVector (F : Frame n d) (r : Fin m) :
    EuclideanSpace ℝ (Fin d × Site m n) :=
  WithLp.toLp 2 fun z ↦ if z.2.1 = r then F.u z.2.2 z.1 else 0

/-- The shared vector is supported on its selected row register.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem sharedVector_apply (F : Frame n d) (r : Fin m)
    (a : Fin d) (s : Site m n) :
    sharedVector F r (a, s) = if s.1 = r then F.u s.2 a else 0 := rfl

/-- The shared vector entry is a frame coordinate when row registers match.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem sharedVector_apply_index (F : Frame n d) (r : Fin m)
    (z : Fin d × Site m n) :
    sharedVector F r z =
      if z.2.1 = r then F.u z.2.2 z.1 else 0 := rfl

/-- Different row-shared vectors are orthogonal, while each has squared norm
exactly `d`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sharedVector_inner (F : Frame n d) (r q : Fin m) :
    inner ℝ (sharedVector F r) (sharedVector F q) =
      if r = q then (d : ℝ) else 0 := by
  simp only [PiLp.inner_apply, Real.inner_apply, sharedVector_apply_index]
  change (∑ z : Fin d × Site m n,
    (if z.2.1 = r then F.u z.2.2 z.1 else 0) *
      (if z.2.1 = q then F.u z.2.2 z.1 else 0)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  by_cases hrq : r = q
  · subst q
    simp
    exact sum_frame_coordinate_sq_eq_dim F
  · simp [hrq, Ne.symm hrq]

/-- The shared vector has squared norm equal to the frame dimension.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem sharedVector_normSq (F : Frame n d) (r : Fin m) :
    inner ℝ (sharedVector F r) (sharedVector F r) = (d : ℝ) := by
  simpa using sharedVector_inner F r r

/-- One literal rank-one matrix `|w_r><w_r|`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def sharedRankOne (F : Frame n d) (r : Fin m) :
    Matrix (Fin d × Site m n) (Fin d × Site m n) ℝ :=
  fun out inp ↦ sharedVector F r out * sharedVector F r inp

/-- The literal one-particle positive matrix `Q = Σ_r |w_r><w_r|`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def sharedQ (F : Frame n d) :
    Matrix (Fin d × Site m n) (Fin d × Site m n) ℝ :=
  ∑ r, sharedRankOne F r

/-- The one-particle operator has entries given by the frame outer product in each row register.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem sharedQ_apply (F : Frame n d)
    (out inp : Fin d × Site m n) :
    sharedQ F out inp =
      if out.2.1 = inp.2.1 then
        F.u out.2.2 out.1 * F.u inp.2.2 inp.1
      else 0 := by
  classical
  simp only [sharedQ, sharedRankOne, Matrix.sum_apply,
    sharedVector_apply_index]
  by_cases hrow : out.2.1 = inp.2.1
  · rw [if_pos hrow]
    simp [hrow]
  · rw [if_neg hrow]
    apply Finset.sum_eq_zero
    intro r _hr
    by_cases hout : out.2.1 = r
    · have hin : inp.2.1 ≠ r := by
        intro heq
        exact hrow (hout.trans heq.symm)
      simp [hout, hin]
    · simp [hout]

end NLAlib.SparseFock.LightSectorConcrete
