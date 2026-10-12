import NLAlib.Matrix.Spectral.RealSchurCanonical

/-!
# Real normal matrices preserve Schur block boundaries

A real normal matrix with a zero lower-left corner has zero upper-right
corner. Applied at the boundaries of a real Schur form, this gives a direct
sum of scalar and two-dimensional normal blocks.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- A real normal upper block triangular matrix has zero upper-right
block. The leading Gram-block trace forces its Frobenius mass to vanish.
Horn–Johnson 2013, Lemma 2.5.2; real normal form helper. -/
theorem eq_zero_of_real_normal_upper_fromBlocks {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ} {C : Matrix m n ℝ}
    (hM : Matrix.fromBlocks A C 0 B * (Matrix.fromBlocks A C 0 B)ᵀ =
      (Matrix.fromBlocks A C 0 B)ᵀ * Matrix.fromBlocks A C 0 B) : C = 0 := by
  have h := congrArg (fun M : Matrix (m ⊕ n) (m ⊕ n) ℝ => M.toBlocks₁₁.trace) hM
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.transpose_zero, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, Matrix.trace_add] at h
  have htr : (C * Cᵀ).trace = 0 := by
    rw [Matrix.trace_mul_comm A Aᵀ] at h
    exact add_left_cancel (by simpa only [add_zero] using h)
  apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using htr

/-- If a real normal matrix has zero entries from the complement of a
coordinate set into that set, the reverse cross entries also vanish.
Horn–Johnson 2013, Lemma 2.5.2; arbitrary finite coordinate cut. -/
theorem eq_zero_of_real_normal_cut {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A * Aᵀ = Aᵀ * A) (p : n → Prop)
    (hzero : ∀ i j, ¬p i → p j → A i j = 0) :
    ∀ i j, p i → ¬p j → A i j = 0 := by
  classical
  let e := Equiv.sumCompl p
  let M := A.submatrix e e
  have hM : M * Mᵀ = Mᵀ * M := by
    simp only [M, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hA]
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    exact hzero i.val j.val i.property j.property
  have hblock : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h21]
  have h12 : M.toBlocks₁₂ = 0 := by
    apply eq_zero_of_real_normal_upper_fromBlocks (A := M.toBlocks₁₁) (B := M.toBlocks₂₂)
    simpa only [← hblock] using hM
  intro i j hi hj
  exact congrArg (fun N : Matrix {i // p i} {j // ¬p j} ℝ => N ⟨i, hi⟩ ⟨j, hj⟩) h12

/-- A zero subdiagonal boundary of a real normal quasitriangular matrix
separates actual orthogonal diagonal blocks. Horn–Johnson 2013,
Lemma 2.5.2; real normal Schur helper. -/
theorem real_normal_quasi_cut_eq_zero {k r : ℕ}
    {T : Matrix (Fin k) (Fin k) ℝ} (hT : IsUpperQuasiTriangular T)
    (hN : T * Tᵀ = Tᵀ * T)
    (hboundary : ∀ i j : Fin k, i.val = r → j.val + 1 = r → T i j = 0) :
    ∀ i j : Fin k, i.val < r → r ≤ j.val → T i j = 0 := by
  have hzero : ∀ i j : Fin k, ¬i.val < r → j.val < r → T i j = 0 := by
    intro i j hi hj
    by_cases hij : j.val + 1 < i.val
    · exact hT.1 i j hij
    · exact hboundary i j (by omega) (by omega)
  intro i j hi hj
  exact eq_zero_of_real_normal_cut hN (fun i => i.val < r) hzero i j hi (by omega)

/-- A real normal quasitriangular matrix has no entries above the first
superdiagonal. Horn–Johnson 2013, Lemma 2.5.2 and Theorem 2.5.4. -/
theorem real_normal_quasi_eq_zero_above_superdiagonal {k : ℕ}
    {T : Matrix (Fin k) (Fin k) ℝ} (hT : IsUpperQuasiTriangular T)
    (hN : T * Tᵀ = Tᵀ * T) (i j : Fin k) (hij : i.val + 1 < j.val) : T i j = 0 := by
  let l : Fin k := ⟨i.val + 1, by omega⟩
  by_cases hli : T l i = 0
  · apply real_normal_quasi_cut_eq_zero hT hN (r := i.val + 1) ?_ i j (by omega) (by omega)
    intro a b ha hb
    have ha' : a = l := Fin.ext ha
    have hb' : b = i := Fin.ext (by omega)
    simpa only [ha', hb'] using hli
  · apply real_normal_quasi_cut_eq_zero hT hN (r := i.val + 2) ?_ i j (by omega) (by omega)
    intro a b ha hb
    have hb' : b = l := Fin.ext (by dsimp [l]; omega)
    subst b
    exact (hT.2 a l i (by dsimp [l]; omega) (by rfl)).resolve_right hli

/-- In a real normal quasitriangular matrix, a zero subdiagonal entry has
a zero reflected superdiagonal entry. Horn–Johnson 2013, Lemma 2.5.2. -/
theorem real_normal_quasi_eq_zero_of_subdiagonal_eq_zero {k : ℕ}
    {T : Matrix (Fin k) (Fin k) ℝ} (hT : IsUpperQuasiTriangular T)
    (hN : T * Tᵀ = Tᵀ * T) {i j : Fin k} (hij : i.val + 1 = j.val)
    (hji : T j i = 0) : T i j = 0 := by
  apply real_normal_quasi_cut_eq_zero hT hN (r := j.val) ?_ i j (by omega) le_rfl
  intro a b ha hb
  have ha' : a = j := Fin.ext ha
  have hb' : b = i := Fin.ext (by omega)
  simpa only [ha', hb'] using hji

end NLAlib
