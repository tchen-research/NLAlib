import NLAlib.Matrix.InterlacingSymmetricConverse

/-!
# Complete converse interlacing

Every weakly interlacing target spectrum is realized by the required border
or rank-one update of a prescribed real symmetric matrix. Characteristic
polynomials certify multiplicities and traces certify exact coupling size.
-/

noncomputable section
set_option autoImplicit false
open Polynomial
open scoped Matrix
namespace NLAlib

/-- Complete converse interlacing for a prescribed real symmetric matrix:
every weakly interlacing target list is realized by a symmetric border,
a positive rank-one update, or a negative rank-one update, according to
its orientation. Exact characteristic polynomials retain every algebraic
multiplicity. The border scalar and squared Euclidean coupling norms equal
the corresponding differences of spectral sums. Empty matrices, singleton
dimensions, repeated original and target roots, zero couplings and all weak
equalities are included. The supplied original list is certified to be the
actual complete ordered spectrum by its characteristic factorization.
Horn–Johnson 2013, Theorems 4.3.21 and 4.3.26; derivations Section herm:converse.
atlas: interlacing-converse -/
theorem interlacing_converse_properties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (d : Fin (Fintype.card ι) → ℝ) (hd : Monotone d)
    (hchar : A.charpoly = ∏ i, (X - C (d i))) :
    (∀ b : Fin (Fintype.card ι + 1) → ℝ, Monotone b →
      (∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ) →
      ∃ v : ι → ℝ, ∃ a : ℝ,
        (Matrix.fromBlocks A (Matrix.replicateCol (Fin 1) v)
          (Matrix.replicateRow (Fin 1) v) (Matrix.of (fun _ _ : Fin 1 => a))).charpoly =
          (∏ j, (X - C (b j))) ∧ a = (∑ i, b i) - ∑ i, d i) ∧
    (∀ b : Fin (Fintype.card ι) → ℝ, Monotone b → (∀ i, d i ≤ b i) →
      (∀ i j, i.val + 1 = j.val → b i ≤ d j) →
      ∃ v : ι → ℝ, (A + Matrix.vecMulVec v v).charpoly = (∏ j, (X - C (b j))) ∧
        (∑ i, (v i) ^ 2) = (∑ i, b i) - ∑ i, d i) ∧
    (∀ b : Fin (Fintype.card ι) → ℝ, Monotone b → (∀ i, b i ≤ d i) →
      (∀ i j, i.val + 1 = j.val → d i ≤ b j) →
      ∃ v : ι → ℝ, (A - Matrix.vecMulVec v v).charpoly = (∏ j, (X - C (b j))) ∧
        (∑ i, (v i) ^ 2) = (∑ i, d i) - ∑ i, b i) := by
  exact ⟨fun b hb h => exists_bordered_charpoly_of_interlacing A hA d b hd hb hchar h,
    fun b hb hlo hhi => exists_add_vecMulVec_charpoly_of_interlacing A hA d b hd hb hchar hlo hhi,
    fun b hb hlo hhi => exists_sub_vecMulVec_charpoly_of_interlacing A hA d b hd hb hchar hlo hhi⟩

end NLAlib
