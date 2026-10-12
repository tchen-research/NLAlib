import NLAlib.Matrix.Norms.NuclearNorm
/-!
# Nuclear norm on arbitrary finite matrix indices

Sharp comparisons, norm axioms and attained nuclear–spectral duality are
transported without dimension or full-rank restrictions.
Source: Horn–Johnson (1991), Corollary 3.4.4; Bhatia (1997), §IV.2.
Atlas: `ky-fan-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- Relabeling rows and columns preserves the real Frobenius pairing. -/
theorem frobInner_reindex {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A B : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    frobInner (A.reindex em en) (B.reindex em en) = frobInner A B := by
  simp only [frobInner, Matrix.reindex_apply, Matrix.submatrix_apply]
  calc
    (∑ i : p, ∑ j : q, A (em.symm i) (en.symm j) * B (em.symm i) (en.symm j)) =
        ∑ i : m, ∑ j : q, A i (en.symm j) * B i (en.symm j) :=
      em.symm.sum_comp (fun i => ∑ j : q, A i (en.symm j) * B i (en.symm j))
    _ = ∑ i : m, ∑ j : n, A i j * B i j :=
      Finset.sum_congr rfl (fun i _ => en.symm.sum_comp (fun j => A i j * B i j))

/-- Relabeling rows and columns preserves the nuclear norm. -/
theorem nuclearNorm_reindex {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    nuclearNorm (A.reindex em en) = nuclearNorm A := by
  simp only [nuclearNorm, kyFanNorm_reindex, ← Fintype.card_congr em, ← Fintype.card_congr en]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The Frobenius norm is at most the nuclear norm on every finite matrix space. -/
theorem frobNorm_le_nuclearNorm (A : Matrix m n ℝ) : frobNorm A ≤ nuclearNorm A := by
  have h := frobNorm_le_nuclearNorm_fin (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  rwa [frobNorm_reindex, nuclearNorm_reindex] at h

/-- The spectral norm is at most the nuclear norm, including empty matrix spaces. -/
theorem specNorm_le_nuclearNorm (A : Matrix m n ℝ) : specNorm A ≤ nuclearNorm A :=
  (specNorm_le_frobNorm A).trans (frobNorm_le_nuclearNorm A)

/-- The sharp actual-rank nuclear-to-spectral comparison on finite matrix indices. -/
theorem nuclearNorm_le_rank_mul_specNorm (A : Matrix m n ℝ) :
    nuclearNorm A ≤ (A.rank : ℝ) * specNorm A := by
  have h := nuclearNorm_le_rank_mul_specNorm_fin (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  rwa [nuclearNorm_reindex, Matrix.rank_reindex, specNorm_reindex] at h

omit [DecidableEq m] in
/-- The sharp square-root-rank nuclear-to-Frobenius comparison on finite indices. -/
theorem nuclearNorm_le_sqrt_rank_mul_frobNorm (A : Matrix m n ℝ) :
    nuclearNorm A ≤ Real.sqrt A.rank * frobNorm A := by
  have h := nuclearNorm_le_sqrt_rank_mul_frobNorm_fin
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  rwa [nuclearNorm_reindex, Matrix.rank_reindex, frobNorm_reindex] at h

omit [DecidableEq m] in
/-- The nuclear norm is subadditive. -/
theorem nuclearNorm_add_le (A B : Matrix m n ℝ) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := kyFanNorm_add_le A B _

omit [DecidableEq m] in
/-- The nuclear norm is absolutely homogeneous. -/
theorem nuclearNorm_smul (A : Matrix m n ℝ) (c : ℝ) : nuclearNorm (c • A) = |c| * nuclearNorm A :=
  kyFanNorm_smul A c _

/-- The nuclear norm is a genuine norm, including the unique norm on an empty
matrix space. -/
theorem nuclearNorm_eq_zero_iff (A : Matrix m n ℝ) : nuclearNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hn : specNorm A = 0 := le_antisymm (by simpa [h] using specNorm_le_nuclearNorm A)
      (specNorm_nonneg A)
    exact norm_eq_zero.mp (by simpa only [specNorm_eq_norm] using hn)
  · rintro rfl
    exact kyFanNorm_zero_matrix _

/-- Orthogonal multiplication on the left preserves the nuclear norm. -/
theorem nuclearNorm_orthogonal_mul (A : Matrix m n ℝ) {U : Matrix m m ℝ}
    (hU : HasOrthonormalCols U) : nuclearNorm (U * A) = nuclearNorm A := kyFanNorm_orthogonal_mul A hU _

omit [DecidableEq m] in
/-- Orthogonal multiplication on the right preserves the nuclear norm. -/
theorem nuclearNorm_mul_orthogonal (A : Matrix m n ℝ) {V : Matrix n n ℝ}
    (hV : HasOrthonormalCols V) : nuclearNorm (A * V) = nuclearNorm A := kyFanNorm_mul_orthogonal A hV _

/-- Transposition preserves the nuclear norm. -/
theorem nuclearNorm_transpose (A : Matrix m n ℝ) : nuclearNorm Aᵀ = nuclearNorm A := by
  rw [nuclearNorm, nuclearNorm, kyFanNorm_transpose, min_comm]

/-- Spectral contractions have pairing at most the nuclear norm, on arbitrary
finite matrix indices. -/
theorem frobInner_le_nuclearNorm_of_specNorm_le_one (A B : Matrix m n ℝ) (hB : specNorm B ≤ 1) :
    frobInner A B ≤ nuclearNorm A := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  have hBn : specNorm (B.reindex em en) ≤ 1 := by rwa [specNorm_reindex]
  have h := frobInner_le_nuclearNorm_of_specNorm_le_one_fin (A.reindex em en) (B.reindex em en) hBn
  rwa [frobInner_reindex, nuclearNorm_reindex] at h

/-- An actual spectral contraction attains nuclear–spectral duality on arbitrary
finite index types, including empty shapes. -/
theorem exists_specNorm_le_one_frobInner_eq_nuclearNorm (A : Matrix m n ℝ) :
    ∃ B : Matrix m n ℝ, specNorm B ≤ 1 ∧ frobInner A B = nuclearNorm A := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  obtain ⟨Bf, hBn, hBpair⟩ := exists_specNorm_le_one_frobInner_eq_nuclearNorm_fin (A.reindex em en)
  let B := Bf.reindex em.symm en.symm
  have hBr : B.reindex em en = Bf := by ext i j; simp [B, Matrix.reindex_apply]
  refine ⟨B, ?_, ?_⟩
  · change specNorm (Bf.reindex em.symm en.symm) ≤ 1
    rwa [specNorm_reindex]
  · have h := frobInner_reindex A B em en
    rw [hBr, hBpair, nuclearNorm_reindex] at h
    exact h.symm

/-- Nuclear–spectral duality with an actual attained greatest value over all
spectral contractions. Horn–Johnson (1991), Corollary 3.4.4.
atlas: ky-fan-norms-def (partial) -/
theorem isGreatest_nuclearNorm_frobInner (A : Matrix m n ℝ) :
    IsGreatest {z : ℝ | ∃ B : Matrix m n ℝ, specNorm B ≤ 1 ∧ frobInner A B = z} (nuclearNorm A) := by
  refine ⟨exists_specNorm_le_one_frobInner_eq_nuclearNorm A, ?_⟩
  rintro z ⟨B, hB, rfl⟩
  exact frobInner_le_nuclearNorm_of_specNorm_le_one A B hB

/-- The bundled nuclear seminorm, with the separating zero criterion proved
above for every finite matrix shape. -/
def nuclearSeminorm : Seminorm ℝ (Matrix m n ℝ) :=
  kyFanSeminorm (min (Fintype.card m) (Fintype.card n))

omit [DecidableEq m] in
/-- The bundled nuclear seminorm agrees with the singular-value sum. -/
@[simp] theorem nuclearSeminorm_apply (A : Matrix m n ℝ) : nuclearSeminorm A = nuclearNorm A := rfl

end NLAlib
