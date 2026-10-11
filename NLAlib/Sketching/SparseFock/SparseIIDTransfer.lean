/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.SparseIIDCoupling
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false

/-!
# Independent-copy lift of the sparse--iid coupling

This file lifts the one-column martingale coupling to every `(g,i)` and proves
the off-diagonal matrix conditional-barycenter identity from TeX lines
237--250.  The restriction `i ≠ j` appears explicitly in the theorem.
-/

open scoped BigOperators InnerProductSpace

namespace NLAlib.SparseFock.SparseIIDTransfer

open ParsevalFrame SparseStackModel SparseStackDistribution SparseIIDCoupling

noncomputable section

/-- Finite-law expectation commutes with a finite-type sum.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_fintype_sum {Omega K : Type*} [Fintype Omega] [Fintype K]
    (mu : FiniteLaw Omega) (f : K → Omega → ℝ) :
    mu.expect (fun omega ↦ ∑ k, f k omega) = ∑ k, mu.expect (f k) := by
  rw [FiniteLaw.expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/-- Finite-law expectation commutes with a finite-set sum.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_finset_sum {Omega K : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (S : Finset K) (f : K → Omega → ℝ) :
    mu.expect (fun omega ↦ ∑ k ∈ S, f k omega) = ∑ k ∈ S, mu.expect (f k) := by
  rw [FiniteLaw.expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/-- A constant scalar factor may be taken outside finite-law expectation.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_mul_const {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (f : Omega → ℝ) (c : ℝ) :
    mu.expect (fun omega ↦ f omega * c) = mu.expect f * c := by
  simp only [FiniteLaw.expect]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  ring

/-- Two distinct coordinates of a literal finite product law factorize.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_two_coordinates
    {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (mu : I → FiniteLaw A) {i j : I} (hij : i ≠ j) (f g : A → ℝ) :
    (FiniteLaw.independentProduct mu).expect (fun x ↦ f (x i) * g (x j)) =
      (mu i).expect f * (mu j).expect g := by
  have h := FiniteLaw.expect_independentProduct_factorizes_on mu {i, j}
    (fun k a ↦ if k = i then f a else g a)
  simpa [hij, Ne.symm hij] using h

/-- An iid array site consists of its physical block and column labels.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev ArraySite (s n : ℕ) := Fin s × Fin n
/-- A selector array assigns one signed hash to every block-column site.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev XArray (b s n : ℕ) := ArraySite s n → SignedHash b
/-- An iid array assigns one ternary block vector to every block-column site.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev YArray (b s n : ℕ) := ArraySite s n → YVector b

/-- Given every sparse selector, the iid vectors are conditionally independent
with the explicit one-column conditional laws.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def conditionalArrayLaw {b s n : ℕ} (hb : 0 < b) (x : XArray b s n) :
    FiniteLaw (YArray b s n) :=
  FiniteLaw.independentProduct (fun z ↦ conditionalYLaw hb (x z))

/-- The unscaled Euclidean iid block vector uses its ternary coordinate values.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def unscaledYVector {b : ℕ} (y : YVector b) : EVec b :=
  WithLp.toLp 2 (fun a ↦ yValue (y a))

/-- The Euclidean iid block vector is scaled by the reciprocal support correction.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def scaledYVector {b : ℕ} (y : YVector b) : EVec b :=
  WithLp.toLp 2 (fun a ↦ cB b * yValue (y a))

/-- The unscaled iid block vector reads its ternary coordinate value.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem unscaledYVector_apply {b : ℕ} (y : YVector b) (a : Fin b) :
    unscaledYVector y a = yValue (y a) := rfl

/-- The scaled iid block vector reads its corrected ternary coordinate value.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem scaledYVector_apply {b : ℕ} (y : YVector b) (a : Fin b) :
    scaledYVector y a = cB b * yValue (y a) := rfl

/-- The inner product of corrected iid vectors is the squared correction times the unscaled inner product.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem scaled_inner_eq {b : ℕ} (y z : YVector b) :
    inner ℝ (scaledYVector y) (scaledYVector z) =
      cB b ^ 2 * inner ℝ (unscaledYVector y) (unscaledYVector z) := by
  simp only [PiLp.inner_apply, Real.inner_apply,
    scaledYVector_apply, unscaledYVector_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Conditional independence plus the one-column barycenter gives the exact
cross-inner-product identity at distinct array sites.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_cross_inner
    {b s n : ℕ} (hb : 0 < b) (x : XArray b s n)
    {z z' : ArraySite s n} (hzz : z ≠ z') :
    (conditionalArrayLaw hb x).expect
        (fun y ↦ inner ℝ (scaledYVector (y z)) (scaledYVector (y z'))) =
      inner ℝ (selectorVector (x z)) (selectorVector (x z')) := by
  unfold conditionalArrayLaw
  simp only [PiLp.inner_apply, Real.inner_apply,
    scaledYVector_apply, selectorVector]
  rw [expect_fintype_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (FiniteLaw.independentProduct (fun q ↦ conditionalYLaw hb (x q))).expect
        (fun y ↦ (cB b * yValue (y z a)) * (cB b * yValue (y z' a))) =
        (conditionalYLaw hb (x z)).expect (fun yz ↦ cB b * yValue (yz a)) *
          (conditionalYLaw hb (x z')).expect (fun yz ↦ cB b * yValue (yz a)) :=
      expect_two_coordinates (mu := fun q ↦ conditionalYLaw hb (x q))
        (i := z) (j := z') hzz
        (fun yz : YVector b ↦ cB b * yValue (yz a))
        (fun yz : YVector b ↦ cB b * yValue (yz a))
    _ = (if a = (x z).1 then (x z).2.val else 0) *
        (if a = (x z').1 then (x z').2.val else 0) := by
      rw [conditional_barycenter_coordinate hb (x z) a,
        conditional_barycenter_coordinate hb (x z') a]

/-- The hollow sparse-selector Gram error from the coupling section, written
directly in signed-basis-vector form.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def sparseVectorError {b s n d : ℕ} (F : Frame n d) (x : XArray b s n) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 / (s : ℝ)) •
    ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
      inner ℝ (selectorVector (x (g, i))) (selectorVector (x (g, j))) •
        ParsevalFrame.outer (F.u i) (F.u j)

/-- The iid-vector hollow Gram error before multiplying by `c_b²`.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def iidVectorError {b s n d : ℕ} (F : Frame n d) (y : YArray b s n) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 / (s : ℝ)) •
    ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
      inner ℝ (unscaledYVector (y (g, i))) (unscaledYVector (y (g, j))) •
        ParsevalFrame.outer (F.u i) (F.u j)

/-- The same iid error with `c_b` placed on each of its two column vectors.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def scaledIIDVectorError {b s n d : ℕ} (F : Frame n d) (y : YArray b s n) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 / (s : ℝ)) •
    ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
      inner ℝ (scaledYVector (y (g, i))) (scaledYVector (y (g, j))) •
        ParsevalFrame.outer (F.u i) (F.u j)

/-- The corrected iid Gram error is the squared scalar correction times the unscaled error.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem scaledIIDVectorError_eq_smul {b s n d : ℕ}
    (F : Frame n d) (y : YArray b s n) :
    scaledIIDVectorError F y = cB b ^ 2 • iidVectorError F y := by
  ext a c
  simp only [scaledIIDVectorError, iidVectorError, Matrix.smul_apply,
    Matrix.sum_apply, ParsevalFrame.outer_apply, smul_eq_mul]
  simp_rw [scaled_inner_eq]
  simp_rw [Finset.mul_sum]
  ring

/-- Entrywise expectation of a finite random matrix.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def matrixExpectation {Omega A : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (M : Omega → Matrix A A ℝ) : Matrix A A ℝ :=
  fun a c ↦ mu.expect (fun omega ↦ M omega a c)

/-- Exact off-diagonal conditional transfer.  No diagonal term is present,
and the proof uses `i ≠ j` to invoke independence at two distinct sites.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_matrix_transfer {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (x : XArray b s n) :
    matrixExpectation (conditionalArrayLaw hb x) (scaledIIDVectorError F) =
      sparseVectorError F x := by
  ext a c
  simp only [matrixExpectation, scaledIIDVectorError, sparseVectorError,
    Matrix.smul_apply, Matrix.sum_apply, ParsevalFrame.outer_apply, smul_eq_mul]
  rw [FiniteLaw.expect_smul]
  congr 1
  rw [expect_fintype_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [expect_fintype_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expect_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [expect_mul_const]
  rw [conditional_cross_inner hb x (hzz := by
    intro hsite
    exact (Ne.symm (Finset.mem_erase.mp hj).1) (congrArg Prod.snd hsite))]

/-- Swapping the two indices preserves an ordered off-diagonal sum.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_offDiagonal_swap {A : Type*} [AddCommMonoid A]
    {n : ℕ} (f : Fin n → Fin n → A) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, f j i := by
  classical
  have expand (g : Fin n → Fin n → A) :
      (∑ i, ∑ j ∈ Finset.univ.erase i, g i j) =
        ∑ i, ∑ j, if j ≠ i then g i j else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
  rw [expand f, expand (fun i j ↦ f j i), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp [hij, Ne.symm]

/-- The literal selector-vector Gram error is symmetric.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseVectorError_symmetric {b s n d : ℕ}
    (F : Frame n d) (x : XArray b s n) :
    (sparseVectorError F x).transpose = sparseVectorError F x := by
  ext a c
  simp only [Matrix.transpose_apply, sparseVectorError, Matrix.smul_apply,
    Matrix.sum_apply, ParsevalFrame.outer_apply, smul_eq_mul]
  apply congrArg ((1 / (s : ℝ)) * ·)
  apply Finset.sum_congr rfl
  intro g _
  rw [sum_offDiagonal_swap]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm]
  ring

/-- The literal iid-vector Gram error is symmetric.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem iidVectorError_symmetric {b s n d : ℕ}
    (F : Frame n d) (y : YArray b s n) :
    (iidVectorError F y).transpose = iidVectorError F y := by
  ext a c
  simp only [Matrix.transpose_apply, iidVectorError, Matrix.smul_apply,
    Matrix.sum_apply, ParsevalFrame.outer_apply, smul_eq_mul]
  apply congrArg ((1 / (s : ℝ)) * ·)
  apply Finset.sum_congr rfl
  intro g _
  rw [sum_offDiagonal_swap]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm]
  ring

/-- The corrected iid-vector Gram error is symmetric.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem scaledIIDVectorError_symmetric {b s n d : ℕ}
    (F : Frame n d) (y : YArray b s n) :
    (scaledIIDVectorError F y).transpose = scaledIIDVectorError F y := by
  rw [scaledIIDVectorError_eq_smul]
  ext a c
  simp only [Matrix.transpose_apply, Matrix.smul_apply]
  have hs := congrFun (congrFun (iidVectorError_symmetric F y) a) c
  simp only [Matrix.transpose_apply] at hs
  rw [hs]

/-- Real symmetric matrices as an actual real vector subspace.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def symmetricMatrices (d : ℕ) : Submodule ℝ (Matrix (Fin d) (Fin d) ℝ) where
  carrier := {A | A.transpose = A}
  zero_mem' := by ext; rfl
  add_mem' := by
    intro A B hA hB
    ext a c
    have ha := congrFun (congrFun hA a) c
    have hb := congrFun (congrFun hB a) c
    simp only [Matrix.transpose_apply] at ha hb
    change A c a + B c a = A a c + B a c
    rw [ha, hb]
  smul_mem' := by
    intro r A hA
    ext a c
    have ha := congrFun (congrFun hA a) c
    simp only [Matrix.transpose_apply, Matrix.smul_apply] at ha ⊢
    rw [ha]

/-- The finite symmetric-matrix space records the real matrix together with its symmetry proof.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev SymmetricMatrix (d : ℕ) := symmetricMatrices d

/-- The selector-vector Gram error is bundled as a symmetric matrix.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def sparseSymmetricError {b s n d : ℕ}
    (F : Frame n d) (x : XArray b s n) : SymmetricMatrix d :=
  ⟨sparseVectorError F x, sparseVectorError_symmetric F x⟩

/-- The corrected iid Gram error is bundled as a symmetric matrix.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def scaledIIDSymmetricError {b s n d : ℕ}
    (F : Frame n d) (y : YArray b s n) : SymmetricMatrix d :=
  ⟨scaledIIDVectorError F y, scaledIIDVectorError_symmetric F y⟩

/-- Barycenter of a finite law in any real vector space.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def barycenter {Omega E : Type*} [Fintype Omega]
    [AddCommGroup E] [Module ℝ E]
    (mu : FiniteLaw Omega) (p : Omega → E) : E :=
  ∑ omega, mu.weight omega • p omega

/-- Finite Jensen inequality for the project's explicit normalized weights.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem finite_jensen {Omega E : Type*} [Fintype Omega]
    [AddCommGroup E] [Module ℝ E]
    (mu : FiniteLaw Omega) (p : Omega → E) (Phi : E → ℝ)
    (hPhi : ConvexOn ℝ Set.univ Phi) :
    Phi (barycenter mu p) ≤ mu.expect (fun omega ↦ Phi (p omega)) := by
  simpa [barycenter, FiniteLaw.expect, smul_eq_mul] using
    hPhi.map_sum_le (t := Finset.univ) (w := mu.weight) (p := p)
      (fun i _ ↦ mu.weight_nonneg i) mu.sum_weight (fun _ _ ↦ Set.mem_univ _)

/-- The subtype barycenter is the entrywise matrix expectation.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coe_barycenter_scaledIID {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (x : XArray b s n) :
    ((barycenter (conditionalArrayLaw hb x) (scaledIIDSymmetricError F) :
        SymmetricMatrix d) : Matrix (Fin d) (Fin d) ℝ) =
      matrixExpectation (conditionalArrayLaw hb x) (scaledIIDVectorError F) := by
  ext a c
  simp only [barycenter, matrixExpectation, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Matrix.sum_apply, Matrix.smul_apply,
    scaledIIDSymmetricError, FiniteLaw.expect, smul_eq_mul]

/-- The conditional corrected iid matrix barycenter equals the literal selector-vector error.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem barycenter_scaledIID_eq_sparse {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (x : XArray b s n) :
    barycenter (conditionalArrayLaw hb x) (scaledIIDSymmetricError F) =
      sparseSymmetricError F x := by
  apply Subtype.ext
  rw [coe_barycenter_scaledIID hb F x]
  exact conditional_matrix_transfer hb F x

/-- Pointwise conditional Jensen on the correct vector space of real
symmetric matrices.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_convex_order {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (x : XArray b s n)
    (Phi : SymmetricMatrix d → ℝ) (hPhi : ConvexOn ℝ Set.univ Phi) :
    Phi (sparseSymmetricError F x) ≤
      (conditionalArrayLaw hb x).expect
        (fun y ↦ Phi (scaledIIDSymmetricError F y)) := by
  rw [← barycenter_scaledIID_eq_sparse hb F x]
  exact finite_jensen (conditionalArrayLaw hb x)
    (scaledIIDSymmetricError F) Phi hPhi

end

end NLAlib.SparseFock.SparseIIDTransfer
