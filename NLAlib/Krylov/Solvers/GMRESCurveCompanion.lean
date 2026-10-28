import NLAlib.Krylov.Solvers.GMRESCurveBasis

/-!
# Prescribed spectrum and coordinate Krylov powers

Conjugating the companion matrix by the explicit GPS basis preserves every
prescribed eigenvalue, including multiplicity, while giving the consecutive
coordinate powers needed by the native GMRES geometry.
Source: Greenbaum--Pták--Strakoš (1996), constructive proof.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
open Polynomial Matrix Finset
namespace NLAlib

/-- The polynomial with the prescribed spectrum, including multiplicities. -/
def gmresCurveSpectrumPolynomial {n : ℕ} (ev : Fin n → ℂ) : ℂ[X] :=
  Lagrange.nodal Finset.univ ev

/-- The spectrum polynomial has exactly the requested dimension. -/
theorem natDegree_gmresCurveSpectrumPolynomial {n : ℕ} (ev : Fin n → ℂ) :
    (gmresCurveSpectrumPolynomial ev).natDegree = n := by
  simp [gmresCurveSpectrumPolynomial,Lagrange.natDegree_nodal]

/-- The companion matrix on the requested finite coordinate type. -/
def gmresCurveCompanion {n : ℕ} (ev : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex (finCongr (natDegree_gmresCurveSpectrumPolynomial ev))
    (finCongr (natDegree_gmresCurveSpectrumPolynomial ev))
      (companionMatrix (gmresCurveSpectrumPolynomial ev))

/-- The companion matrix has the exact prescribed characteristic polynomial.
atlas: gmres-any-convergence-curve (partial) -/
theorem charpoly_gmresCurveCompanion {n : ℕ} (ev : Fin n → ℂ) :
    (gmresCurveCompanion ev).charpoly = ∏ i : Fin n, (X-C (ev i)) := by
  rw [gmresCurveCompanion,Matrix.charpoly_reindex,
    charpoly_companionMatrix (p := gmresCurveSpectrumPolynomial ev)
      (show (gmresCurveSpectrumPolynomial ev).Monic from Lagrange.nodal_monic)]
  rfl

private theorem gmresCurveCompanion_apply {n : ℕ} (ev : Fin n → ℂ) (i j : Fin n) :
    gmresCurveCompanion ev i j =
      if j.val+1=n then -(gmresCurveSpectrumPolynomial ev).coeff i.val
      else if i.val=j.val+1 then 1 else 0 := by
  simp only [gmresCurveCompanion,Matrix.reindex_apply,Matrix.submatrix_apply,
    companionMatrix,finCongr_symm,finCongr_apply_coe,natDegree_gmresCurveSpectrumPolynomial]

/-- The non-final companion columns are the exact coordinate shift. -/
theorem gmresCurveCompanion_mulVec_single {n : ℕ} (ev : Fin n → ℂ) (j : Fin (n-1)) :
    gmresCurveCompanion ev *ᵥ Pi.single ⟨j.val,by have := j.isLt; omega⟩ (1 : ℂ) =
      Pi.single ⟨j.val+1,by have := j.isLt; omega⟩ (1 : ℂ) := by
  rw [Matrix.mulVec_single_one]
  funext i
  change gmresCurveCompanion ev i ⟨j.val,by have := j.isLt; omega⟩ = _
  have hnot : j.val+1 ≠ n := by have := j.isLt; omega
  rw [gmresCurveCompanion_apply,if_neg hnot]
  simp only [Pi.single_apply,Fin.ext_iff]

/-- The explicit matrix with prescribed spectrum and prescribed coordinate
Krylov geometry. -/
def gmresCurveMatrix {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ) (ev : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  gmresCurveBasis hn b * gmresCurveCompanion ev * (gmresCurveBasis hn b)⁻¹

/-- Similarity preserves the exact prescribed spectrum, including repetitions.
atlas: gmres-any-convergence-curve (partial) -/
theorem charpoly_gmresCurveMatrix {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : b ⟨n-1,by omega⟩ ≠ 0) (ev : Fin n → ℂ) :
    (gmresCurveMatrix hn b ev).charpoly = ∏ i : Fin n, (X-C (ev i)) := by
  have hW := isUnit_gmresCurveBasis hn b hb
  rw [gmresCurveMatrix,Matrix.charpoly_mul_comm,← mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hW),one_mul,
    charpoly_gmresCurveCompanion]

/-- The similarity construction transports every non-final companion power. -/
theorem pow_gmresCurveMatrix_mulVec {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : b ⟨n-1,by omega⟩ ≠ 0) (ev : Fin n → ℂ) (k : ℕ) (hk : k < n) :
    (gmresCurveMatrix hn b ev)^k *ᵥ b =
      gmresCurveBasis hn b *ᵥ Pi.single ⟨k,hk⟩ (1 : ℂ) := by
  have hW := isUnit_gmresCurveBasis hn b hb
  induction k with
  | zero =>
    rw [pow_zero,Matrix.one_mulVec]
    exact (gmresCurveBasis_mulVec_first hn b).symm
  | succ k ih =>
    rw [pow_succ',← Matrix.mulVec_mulVec,ih (by omega),gmresCurveMatrix]
    simp only [← Matrix.mulVec_mulVec]
    have hinv : (gmresCurveBasis hn b)⁻¹ *ᵥ
        (gmresCurveBasis hn b *ᵥ Pi.single ⟨k,by omega⟩ (1 : ℂ)) =
          Pi.single ⟨k,by omega⟩ (1 : ℂ) := by
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hW),Matrix.one_mulVec]
    rw [hinv]
    have hs := gmresCurveCompanion_mulVec_single ev (⟨k,by omega⟩ : Fin (n-1))
    rw [hs]

/-- The actual powers are consecutive coordinate vectors, independent of the
prescribed spectrum. This is the full native geometry needed for GPS.
atlas: gmres-any-convergence-curve (partial) -/
theorem pow_succ_gmresCurveMatrix_mulVec {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : b ⟨n-1,by omega⟩ ≠ 0) (ev : Fin n → ℂ) (j : Fin (n-1)) :
    (gmresCurveMatrix hn b ev)^(j.val+1) *ᵥ b =
      Pi.single ⟨j.val,by have := j.isLt; omega⟩ (1 : ℂ) := by
  rw [pow_gmresCurveMatrix_mulVec hn b hb ev _ (by have := j.isLt; omega)]
  exact gmresCurveBasis_mulVec_succ hn b j

end NLAlib
