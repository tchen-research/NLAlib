import NLAlib.Matrix.Spectral.SaddlePointSpectrum
import NLAlib.Matrix.Structured.SchurWhitening
import NLAlib.Krylov.Solvers.GMRESIterate

/-!
# Native Schur-preconditioned spectra and finite Krylov termination

The exact leading block is retained. The symmetric system uses the inverse square
root of `diag(A,Ŝ)`; the triangular system uses the inverse of `[A 0; B -S]`.
Source: Benzi--Golub--Liesen (2005), Sections 10.1.1--10.1.2.
-/

noncomputable section
open scoped Matrix Polynomial MatrixOrder ComplexOrder
open Polynomial
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The actual Hermitian symmetrically preconditioned saddle-point matrix. -/
def schurSymmetricPreconditioned (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (Shat : Matrix m m 𝕜) : Matrix (n ⊕ m) (n ⊕ m) 𝕜 :=
  let R := cfc (fun x => (Real.sqrt x)⁻¹) (Matrix.fromBlocks A 0 0 Shat)
  R * kktMatrix A B * R

open scoped Matrix.Norms.L2Operator in
/-- The complete characteristic-root multiset of the actual symmetrically
preconditioned system. The Gram eigenvalues equal those of `Ŝ⁻¹ᐟ² S Ŝ⁻¹ᐟ²`
by `saddle_coupling_mul_conjTranspose`.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem roots_charpoly_schurSymmetricPreconditioned [Nonempty n] [Nonempty m]
    {A : Matrix n n 𝕜} {Shat : Matrix m m 𝕜} (hA : A.PosDef) (hS : Shat.PosDef)
    {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m) :
    let C := cfc (fun x => (Real.sqrt x)⁻¹) Shat * B * cfc (fun x => (Real.sqrt x)⁻¹) A
    let mu := (Matrix.isHermitian_mul_conjTranspose_self C).eigenvalues
    (schurSymmetricPreconditioned A B Shat).charpoly.roots =
      (Fintype.card n - Fintype.card m) • ({1} : Multiset 𝕜) +
        Finset.univ.val.bind (fun i : m =>
          {(saddleEigenvaluePlus (mu i) : 𝕜)} + {(saddleEigenvalueMinus (mu i) : 𝕜)}) := by
  dsimp only
  rw [schurSymmetricPreconditioned, symmetric_saddle_preconditioning_eq hA hS]
  exact roots_charpoly_kktMatrix_one _ (hB ▸ B.rank_le_card_width)

/-- The actual preconditioned system is Hermitian.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem isHermitian_schurSymmetricPreconditioned [Nonempty n] [Nonempty m]
    {A : Matrix n n 𝕜} {Shat : Matrix m m 𝕜} (hA : A.PosDef) (hS : Shat.PosDef)
    (B : Matrix m n 𝕜) : (schurSymmetricPreconditioned A B Shat).IsHermitian := by
  rw [schurSymmetricPreconditioned, symmetric_saddle_preconditioning_eq hA hS, kktMatrix]
  exact Matrix.isHermitian_one.fromBlocks (by simp) Matrix.isHermitian_zero

/-- The multiplicity of eigenvalue `1` is exactly `n-m`, with no additional unit
eigenvalues hidden in the paired spectrum.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem count_one_roots_schurSymmetricPreconditioned [Nonempty n] [Nonempty m]
    {A : Matrix n n 𝕜} {Shat : Matrix m m 𝕜} (hA : A.PosDef) (hS : Shat.PosDef)
    {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m) :
    (schurSymmetricPreconditioned A B Shat).charpoly.roots.count 1 =
      Fintype.card n - Fintype.card m := by
  rw [schurSymmetricPreconditioned, symmetric_saddle_preconditioning_eq hA hS]
  exact count_one_roots_charpoly_kktMatrix_one (posDef_saddle_coupling_gram hA hS hB)
    (hB ▸ B.rank_le_card_width)

open scoped Matrix.Norms.L2Operator in
/-- The paired positive and negative eigenvalues lie in the advertised intervals
under relative Loewner bounds on the actual Schur complement.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem schurSymmetricPreconditioned_eigenvalue_intervals [Nonempty n] [Nonempty m]
    {A : Matrix n n 𝕜} {Shat : Matrix m m 𝕜} (hA : A.PosDef) (hS : Shat.PosDef)
    {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m) {a b : ℝ}
    (ha : a • Shat ≤ saddleSchurComplement A B)
    (hb : saddleSchurComplement A B ≤ b • Shat) {lam : ℝ}
    (hlam : (lam : 𝕜) ∈ spectrum 𝕜 (schurSymmetricPreconditioned A B Shat)) :
    (lam = 1 ∧ Fintype.card m < Fintype.card n) ∨
      lam ∈ Set.Icc (saddleEigenvaluePlus a) (saddleEigenvaluePlus b) ∨
      lam ∈ Set.Icc (saddleEigenvalueMinus b) (saddleEigenvalueMinus a) := by
  have hr := (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mpr
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hlam)
  rw [roots_charpoly_schurSymmetricPreconditioned hA hS hB] at hr
  simp only [Multiset.mem_add, Multiset.mem_nsmul, Multiset.mem_singleton,
    Multiset.mem_bind, Finset.mem_val, Finset.mem_univ, true_and] at hr
  rcases hr with ⟨hne, he⟩ | ⟨i, hi | hi⟩
  · exact Or.inl ⟨by exact_mod_cast he, by omega⟩
  · have he := congrArg RCLike.re hi
    simp only [RCLike.ofReal_re] at he
    rw [he]
    have h := saddle_coupling_eigenvalues_mem_Icc hA hS B ha hb i
    exact Or.inr (Or.inl ⟨monotone_saddleEigenvaluePlus h.1, monotone_saddleEigenvaluePlus h.2⟩)
  · have he := congrArg RCLike.re hi
    simp only [RCLike.ofReal_re] at he
    rw [he]
    have h := saddle_coupling_eigenvalues_mem_Icc hA hS B ha hb i
    exact Or.inr (Or.inr ⟨antitone_saddleEigenvalueMinus h.2, antitone_saddleEigenvalueMinus h.1⟩)

omit [Fintype m] [DecidableEq m] in
/-- An annihilating residual polynomial forces exact termination of every native
GMRES minimizer at the specified degree. -/
theorem IsGMRESIterate.residual_eq_zero_of_aeval_eq_zero {M : Matrix n n 𝕜}
    {c x₀ x : n → 𝕜} {q : ℕ} (hx : IsGMRESIterate M c x₀ q x)
    {p : 𝕜[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) (hM : aeval M p = 0) :
    c - M *ᵥ x = 0 := by
  have h := hx.norm_le_aeval hp hp0
  rw [hM, Matrix.zero_mulVec, WithLp.toLp_zero, norm_zero] at h
  exact WithLp.toLp_injective 2 (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- Exact triangular Schur preconditioning gives GMRES termination after at most
two steps for every right-hand side and initializer, over either scalar field.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem gmres_triangular_schur_terminates {A : Matrix n n 𝕜} (hA : A.PosDef)
    {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m)
    {c x₀ x : (n ⊕ m) → 𝕜}
    (hx : IsGMRESIterate ((Matrix.fromBlocks A 0 B (-saddleSchurComplement A B))⁻¹ *
      kktMatrix A B) c x₀ 2 x) :
    c - ((Matrix.fromBlocks A 0 B (-saddleSchurComplement A B))⁻¹ * kktMatrix A B) *ᵥ x = 0 := by
  apply hx.residual_eq_zero_of_aeval_eq_zero (p := (X - 1) ^ 2)
  · compute_degree; norm_num
  · norm_num
  · simpa only [map_pow, map_sub, aeval_X, map_one] using
      triangular_saddle_preconditioning_sub_one_sq hA hB

/-- Exact symmetric Schur preconditioning gives MINRES termination after at most
three steps. MINRES uses the native residual minimizer predicate on the Hermitian
symmetrically preconditioned matrix, with arbitrary right-hand side and initializer.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem minres_symmetric_schur_terminates [Nonempty n] [Nonempty m]
    {A : Matrix n n 𝕜} (hA : A.PosDef) {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m)
    {c x₀ x : (n ⊕ m) → 𝕜}
    (hx : IsGMRESIterate (schurSymmetricPreconditioned A B (saddleSchurComplement A B))
      c x₀ 3 x) :
    c - schurSymmetricPreconditioned A B (saddleSchurComplement A B) *ᵥ x = 0 := by
  apply hx.residual_eq_zero_of_aeval_eq_zero (p := (X - 1) * (X ^ 2 - X - 1))
  · compute_degree; norm_num
  · norm_num
  · simp only [map_mul, map_sub, map_pow, aeval_X, map_one]
    rw [schurSymmetricPreconditioned,
      symmetric_saddle_preconditioning_eq hA (posDef_saddleSchurComplement hA hB)]
    exact kktMatrix_one_annihilator (saddle_coupling_gram_eq_one hA hB)

end NLAlib
