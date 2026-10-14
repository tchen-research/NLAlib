import NLAlib.Krylov.Spaces.Cyclic
import NLAlib.ForMathlib.LinearAlgebra.KernelProducts
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.Polynomial.Splits

/-!
# Geometric simplicity and cyclicity over a splitting field

Kernel dimension is subadditive under composition. Applying this finite
inequality to the linear factors of the minimal polynomial proves the
nonderogatory criterion, including repeated eigenvalues. The converse uses
injectivity of `A-λI` on the first `n-1` Krylov powers.
Source: Horn–Johnson (2013), Theorem 3.3.14; operator derivations, Section 6.
Atlas: `companion-matrix`.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- Over a field where the characteristic polynomial splits, eigenspaces of
dimension at most one force the operator minimal polynomial to have full degree.
Repeated eigenvalues and empty matrices are included.
Source: operator derivations, geometric criterion following (S3).
atlas: companion-matrix (partial) -/
theorem natDegree_minpoly_eq_card_of_finrank_eigenspace_le_one
    (A : Matrix n n K) (hsplit : A.charpoly.Splits)
    (hgeom : ∀ μ : K, Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) ≤ 1) :
    (minpoly K A).natDegree = Fintype.card n := by
  let f := Matrix.toLin' A
  have hs : (minpoly K f).Splits := by
    rw [Matrix.minpoly_toLin']
    exact hsplit.of_dvd (Matrix.charpoly_monic A).ne_zero (Matrix.minpoly_dvd_charpoly A)
  have hbound (l : Multiset K) :
      Module.finrank K (LinearMap.ker (aeval f (l.map (fun μ => X - C μ)).prod)) ≤ l.card := by
    induction l using Multiset.induction_on with
    | empty =>
      rw [Multiset.map_zero, Multiset.prod_zero, aeval_one, Module.End.one_eq_id,
        LinearMap.ker_id]
      simp
    | @cons μ l ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul]
      have h := LinearMap.finrank_ker_comp_le
        (f - algebraMap K (Module.End K (n → K)) μ)
        (aeval f (l.map (fun ν => X - C ν)).prod)
      have hμ := hgeom μ
      rw [Module.End.eigenspace_def] at hμ
      change Module.finrank K (LinearMap.ker
        (f - algebraMap K (Module.End K (n → K)) μ)) ≤ 1 at hμ
      have heval : aeval f (X - C μ) =
          f - algebraMap K (Module.End K (n → K)) μ := by
        rw [map_sub, aeval_X, aeval_C]
      rw [heval, Module.End.mul_eq_comp]
      simp only [Multiset.card_cons]
      omega
  have h := hbound (minpoly K f).roots
  rw [← hs.eq_prod_roots_of_monic (minpoly.monic (Algebra.IsIntegral.isIntegral f)),
    minpoly.aeval, LinearMap.ker_zero, finrank_top,
    Module.finrank_fintype_fun_eq_card, ← hs.natDegree_eq_card_roots,
    Matrix.minpoly_toLin'] at h
  exact le_antisymm (natDegree_minpoly_le_card A) h

/-- A full-grade vector makes every eigenspace at most one-dimensional,
without requiring a splitting field or a simple algebraic spectrum.
Source: operator derivations, geometric criterion following (S3).
atlas: companion-matrix (partial) -/
theorem finrank_eigenspace_le_one_of_krylovGrade_eq_card
    {A : Matrix n n K} {b : n → K} (hb : krylovGrade A b = Fintype.card n) (μ : K) :
    Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) ≤ 1 := by
  let S := krylovSpace A b (Fintype.card n - 1)
  let M : Matrix n n K := A - algebraMap K (Matrix n n K) μ
  let L := M.mulVecLin.comp S.subtype
  have hinj : Function.Injective L := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply Subtype.ext
    have hz : M *ᵥ ((x : n → K) - y) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hxy
    obtain ⟨q, hq, heq⟩ := (mem_krylovSpace_iff A b _ ((x : n → K) - y)).mp
      (S.sub_mem x.property y.property)
    by_cases hq0 : q = 0
    · simp [hq0] at heq
      exact heq
    have hqnat : q.natDegree < Fintype.card n - 1 :=
      (natDegree_lt_iff_degree_lt hq0).mpr hq
    have hprod0 : (X - C μ) * q ≠ 0 := mul_ne_zero (monic_X_sub_C μ).ne_zero hq0
    have hdeg : ((X - C μ) * q).degree < (krylovGrade A b : WithBot ℕ) := by
      rw [degree_eq_natDegree hprod0, natDegree_mul (monic_X_sub_C μ).ne_zero hq0,
        natDegree_X_sub_C, hb]
      exact_mod_cast (show 1 + q.natDegree < Fintype.card n by omega)
    have hann : aeval A ((X - C μ) * q) *ᵥ b = 0 := by
      rw [map_mul, map_sub, aeval_X, aeval_C, ← Matrix.mulVec_mulVec, ← heq]
      exact hz
    exact (hprod0 (eq_zero_of_aeval_mulVec_eq_zero hdeg hann)).elim
  have hdimS : Module.finrank K S = Fintype.card n - 1 := by
    rw [finrank_krylovSpace, hb, min_eq_left (Nat.sub_le _ _)]
  have hdimL : Module.finrank K (LinearMap.range L) = Fintype.card n - 1 :=
    (LinearMap.finrank_range_of_inj hinj).trans hdimS
  have hrange : Module.finrank K (LinearMap.range L) ≤
      Module.finrank K (LinearMap.range M.mulVecLin) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hnull := M.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hnull
  have hker : Module.End.eigenspace (Matrix.toLin' A) μ = LinearMap.ker M.mulVecLin := by
    apply Submodule.ext
    intro v
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
    change A *ᵥ v = μ • v ↔ M *ᵥ v = 0
    simp only [M, Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [hker]
  omega

/-- Over a splitting field, full degree of the minimal polynomial is equivalent
to geometric simplicity of every eigenvalue, including repeated eigenvalues.
The empty-dimensional statement is vacuous on the geometric side.
Source: Horn–Johnson (2013), Theorem 3.3.14; operator derivations, Section 6.
atlas: companion-matrix (partial) -/
theorem natDegree_minpoly_eq_card_iff_finrank_eigenspace_le_one
    (A : Matrix n n K) (hsplit : A.charpoly.Splits) :
    (minpoly K A).natDegree = Fintype.card n ↔
      ∀ μ : K, Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) ≤ 1 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (natDegree_minpoly_eq_card_iff_exists_krylovGrade_eq_card A).mp h
    exact finrank_eigenspace_le_one_of_krylovGrade_eq_card hb
  · exact natDegree_minpoly_eq_card_of_finrank_eigenspace_le_one A hsplit

end NLAlib
