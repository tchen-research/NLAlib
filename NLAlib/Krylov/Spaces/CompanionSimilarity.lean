import NLAlib.Krylov.Spaces.Cyclic

/-!
# Companion similarity in a cyclic basis

The companion representation is expressed through a native Mathlib basis,
allowing arbitrary finite matrix labels. The basis consists of successive
powers of a cyclic vector. Source: Horn–Johnson (2013), Theorem 3.3.14;
operator derivations, (S2)–(S3). Atlas: `companion-matrix`.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A full-grade vector gives a Krylov basis in which the operator is its
characteristic-polynomial companion matrix. Native basis representation is
the similarity interface, including dimension zero and arbitrary finite labels.
Source: operator derivations, (S2)–(S3).
atlas: companion-matrix (partial) -/
theorem exists_basis_toMatrix_eq_companionMatrix_of_krylovGrade_eq_card
    {A : Matrix n n K} {b : n → K} (hb : krylovGrade A b = Fintype.card n) :
    ∃ B : Module.Basis (Fin A.charpoly.natDegree) K (n → K),
      (∀ i, B i = (A ^ (i : ℕ)) *ᵥ b) ∧
      LinearMap.toMatrix B B (Matrix.toLin' A) = companionMatrix A.charpoly := by
  let p := A.charpoly
  let pb := AdjoinRoot.powerBasis' (Matrix.charpoly_monic A)
  have hd : p.natDegree = Fintype.card n := Matrix.charpoly_natDegree_eq_dim A
  have hli : LinearIndependent K (fun i : Fin p.natDegree => (A ^ (i : ℕ)) *ᵥ b) :=
    (linearIndependent_pow_mulVec_iff_le_krylovGrade A b).mpr (by rw [hd, hb])
  have hspan : ⊤ ≤ Submodule.span K
      (Set.range fun i : Fin p.natDegree => (A ^ (i : ℕ)) *ᵥ b) := by
    change ⊤ ≤ krylovSpace A b p.natDegree
    rw [hd, krylovSpace_eq_top_of_krylovGrade_eq_card hb]
  let B₀ := Module.Basis.mk hli hspan
  let e : AdjoinRoot p ≃ₗ[K] (n → K) := pb.basis.equiv B₀ (Equiv.refl _)
  have hμ : minpoly K pb.gen = p := by
    change minpoly K (AdjoinRoot.root p) = p
    rw [AdjoinRoot.minpoly_root (Matrix.charpoly_monic A).ne_zero,
      (Matrix.charpoly_monic A).leadingCoeff, inv_one, C_1, mul_one]
  have hroot : aeval A (minpoly K pb.gen) = 0 := by
    rw [hμ]
    exact Matrix.aeval_self_charpoly A
  let φ : AdjoinRoot p →ₐ[K] Matrix n n K :=
    pb.lift A hroot
  let L : AdjoinRoot p →ₗ[K] (n → K) :=
    { toFun := fun x => φ x *ᵥ b
      map_add' := by intro x y; simp [map_add, Matrix.add_mulVec]
      map_smul' := by intro c x; simp [map_smul, Matrix.smul_mulVec] }
  have hφroot : φ (AdjoinRoot.root p) = A :=
    pb.lift_gen A hroot
  have hLb (i : Fin pb.dim) : L (pb.basis i) = (A ^ (i : ℕ)) *ᵥ b := by
    change φ (pb.basis i) *ᵥ b = _
    rw [pb.basis_eq_pow, map_pow]
    change φ (AdjoinRoot.root p) ^ (i : ℕ) *ᵥ b = _
    rw [hφroot]
  have heL : e.toLinearMap = L := by
    apply pb.basis.ext
    intro i
    change (pb.basis.equiv B₀ (Equiv.refl _)) (pb.basis i) = L (pb.basis i)
    rw [Module.Basis.equiv_apply]
    change (Module.Basis.mk hli hspan) ((Equiv.refl (Fin pb.dim)) i) = L (pb.basis i)
    rw [Module.Basis.mk_apply]
    exact (hLb i).symm
  have hint (x : AdjoinRoot p) : A *ᵥ e x = e (AdjoinRoot.root p * x) := by
    change Matrix.toLin' A (e.toLinearMap x) = e.toLinearMap (AdjoinRoot.root p * x)
    rw [heL]
    change A *ᵥ (φ x *ᵥ b) = φ (AdjoinRoot.root p * x) *ᵥ b
    rw [map_mul, hφroot, Matrix.mulVec_mulVec]
  have hcomp : e.symm.toLinearMap.comp ((Matrix.toLin' A).comp e.toLinearMap) =
      Algebra.lmul K (AdjoinRoot p) (AdjoinRoot.root p) := by
    apply LinearMap.ext
    intro x
    change e.symm (A *ᵥ e x) = AdjoinRoot.root p * x
    rw [hint, e.symm_apply_apply]
  refine ⟨pb.basis.map e, ?_, ?_⟩
  · intro i
    change e (pb.basis i) = _
    change e.toLinearMap (pb.basis i) = _
    rw [heL, hLb]
  · rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right, hcomp,
      ← Algebra.leftMulMatrix_apply]
    exact leftMulMatrix_adjoinRoot_eq_companionMatrix (Matrix.charpoly_monic A)

/-- A matrix has its own characteristic companion representation exactly when
minimal and characteristic polynomials coincide. This is similarity stated through
a native basis and holds over every field, including empty matrices.
Source: Horn–Johnson (2013), Theorem 3.3.14; operator derivations, (S3).
atlas: companion-matrix (partial) -/
theorem minpoly_eq_charpoly_iff_exists_basis_toMatrix_eq_companionMatrix
    (A : Matrix n n K) :
    minpoly K A = A.charpoly ↔
      ∃ B : Module.Basis (Fin A.charpoly.natDegree) K (n → K),
        LinearMap.toMatrix B B (Matrix.toLin' A) = companionMatrix A.charpoly := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (natDegree_minpoly_eq_card_iff_exists_krylovGrade_eq_card A).mp
      ((minpoly_eq_charpoly_iff_natDegree_eq_card A).mp h)
    obtain ⟨B, _, hB⟩ := exists_basis_toMatrix_eq_companionMatrix_of_krylovGrade_eq_card hb
    exact ⟨B, hB⟩
  · rintro ⟨B, hB⟩
    have h := minpoly_companionMatrix (Matrix.charpoly_monic A)
    rw [← hB, LinearMap.minpoly_toMatrix, Matrix.minpoly_toLin'] at h
    exact h

end NLAlib
