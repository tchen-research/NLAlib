import NLAlib.Krylov.Quadrature.Christoffel

/-!
# Christoffel polynomials and conjugate Krylov directions

Weighting the spectral moment functional by `X` is exactly the matrix energy
pairing. For a positive definite matrix it is nondegenerate through the Krylov
grade. Its canonical polynomials produce the unique conjugate directions in
successive graded Krylov spaces, up to nonzero scalar normalizations.
Source: Gautschi (2004), §1.3; operator re-derivations, after AQ15.
-/

noncomputable section
open Polynomial Matrix MeasureTheory
open scoped Matrix
namespace NLAlib
variable {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℝ} {b : m → ℝ}

/-- The actual zero-shift Christoffel Krylov vector is nonzero, belongs to the
next graded Krylov space, and is energy-orthogonal to the preceding space.
Source: Gautschi (2004), CG direction interpretation; operator re-derivations.
atlas: kernel-polynomials-christoffel (partial) -/
theorem christoffelPolynomial_spectralMeasure_krylov_direction
    (hA : A.PosDef) (b : m → ℝ) {k : ℕ} (hk : k < krylovGrade A b) :
    let p := christoffelPolynomial (polynomialIntegral (spectralMeasure hA.isHermitian b)
      (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) 0 k
    aeval A p *ᵥ b ≠ 0 ∧ aeval A p *ᵥ b ∈ krylovSpace A b (k+1) ∧
      ∀ v ∈ krylovSpace A b k, (aeval A p *ᵥ b) ⬝ᵥ (A *ᵥ v) = 0 := by
  let L := polynomialWeightedFunctional
    (polynomialIntegral (spectralMeasure hA.isHermitian b)
      (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) X
  rw [← monicOrthogonalPolynomial_weighted_spectralMeasure_eq_christoffelPolynomial hA b hk]
  have hL : hankelMomentDet L k ≠ 0 :=
    hankelMomentDet_ne_zero_of_posDef_of_le
      (posDef_hankelMomentMatrix_polynomialWeightedFunctional_spectralMeasure_X hA b hk.le) le_rfl
  have hP := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hL
  have hd : (monicOrthogonalPolynomial L k).degree = k := by
    rw [degree_eq_natDegree hP.monic.ne_zero, hP.natDegree_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    exact hP.monic.ne_zero (eq_zero_of_aeval_mulVec_eq_zero (by rw [hd]; exact_mod_cast hk) hzero)
  · apply (mem_krylovSpace_iff A b (k+1) _).mpr
    exact ⟨_, by rw [hd]; exact_mod_cast Nat.lt_succ_self k, rfl⟩
  · intro v hv
    obtain ⟨q, hq, rfl⟩ := (mem_krylovSpace_iff A b k v).mp hv
    rw [← polynomialWeightedFunctional_spectralMeasure_X_mul]
    exact hP.orthogonal q hq

/-- Distinct actual zero-shift Christoffel Krylov vectors are mutually
`A`-conjugate before termination.
Source: operator re-derivations, SPD kernel direction orthogonality.
atlas: kernel-polynomials-christoffel (partial) -/
theorem dotProduct_christoffelPolynomial_spectralMeasure_mulVec_eq_zero
    (hA : A.PosDef) (b : m → ℝ) {i j : ℕ}
    (hi : i < krylovGrade A b) (hj : j < krylovGrade A b) (hij : i ≠ j) :
    (aeval A (christoffelPolynomial (polynomialIntegral (spectralMeasure hA.isHermitian b)
      (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) 0 i) *ᵥ b) ⬝ᵥ
      (A *ᵥ (aeval A (christoffelPolynomial (polynomialIntegral (spectralMeasure hA.isHermitian b)
        (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) 0 j) *ᵥ b)) = 0 := by
  let d := fun k => aeval A (christoffelPolynomial
    (polynomialIntegral (spectralMeasure hA.isHermitian b)
      (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) 0 k) *ᵥ b
  have hD (k : ℕ) (hk : k < krylovGrade A b) :
      d k ∈ krylovSpace A b (k+1) ∧ ∀ v ∈ krylovSpace A b k, d k ⬝ᵥ (A *ᵥ v) = 0 :=
    (christoffelPolynomial_spectralMeasure_krylov_direction hA b hk).2
  change d i ⬝ᵥ (A *ᵥ d j) = 0
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hzero := (hD j hj).2 (d i)
      (krylovSpace_mono A b (by omega : i+1 ≤ j) (hD i hi).1)
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      show Aᵀ = A by rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA.isHermitian,
      dotProduct_comm]
    exact hzero
  · exact (hD i hi).2 (d j)
      (krylovSpace_mono A b (by omega : j+1 ≤ i) (hD j hj).1)

/-- Any nonzero vector in the next Krylov space that is energy-orthogonal to
the preceding space is a nonzero scalar multiple of the actual zero-shift
Christoffel vector. Thus the mathematical conjugate-direction interpretation
requires no chosen normalization or assumed CG recurrence invariant.
Source: operator re-derivations, uniqueness in graded Krylov spaces.
atlas: kernel-polynomials-christoffel (partial) -/
theorem exists_nonzero_smul_christoffelPolynomial_spectralMeasure_of_krylov_direction
    (hA : A.PosDef) (b : m → ℝ) {k : ℕ} (hk : k < krylovGrade A b)
    {d : m → ℝ} (hd0 : d ≠ 0) (hd : d ∈ krylovSpace A b (k+1))
    (horth : ∀ v ∈ krylovSpace A b k, d ⬝ᵥ (A *ᵥ v) = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ d = c • (aeval A
      (christoffelPolynomial (polynomialIntegral (spectralMeasure hA.isHermitian b)
        (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) 0 k) *ᵥ b) := by
  let L := polynomialWeightedFunctional
    (polynomialIntegral (spectralMeasure hA.isHermitian b)
      (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) X
  obtain ⟨p, hp, hpd⟩ := (mem_krylovSpace_iff A b (k+1) d).mp hd
  have hL : hankelMomentDet L k ≠ 0 :=
    hankelMomentDet_ne_zero_of_posDef_of_le
      (posDef_hankelMomentMatrix_polynomialWeightedFunctional_spectralMeasure_X hA b hk.le) le_rfl
  have hpdeg : p.degree ≤ k := by
    apply (degree_le_iff_coeff_zero p _).mpr
    intro j hj
    have hkj : k < j := by exact_mod_cast hj
    exact coeff_eq_zero_of_degree_lt
      (hp.trans_le (by exact_mod_cast (show k+1 ≤ j by omega)))
  have hp' := eq_C_mul_monicOrthogonalPolynomial_of_degree_le_of_orthogonal L hL hpdeg (by
    intro q hq
    rw [polynomialWeightedFunctional_spectralMeasure_X_mul, ← hpd]
    exact horth _ ((mem_krylovSpace_iff A b k _).mpr ⟨q, hq, rfl⟩))
  have heq : d = p.coeff k • (aeval A (monicOrthogonalPolynomial L k) *ᵥ b) := by
    rw [hpd]
    simpa only [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, Matrix.one_mul, Matrix.smul_mulVec] using
      congrArg (fun q : ℝ[X] => aeval A q *ᵥ b) hp'
  refine ⟨p.coeff k, ?_, ?_⟩
  · intro hz
    rw [hz, zero_smul] at heq
    exact hd0 heq
  · simpa only [L, monicOrthogonalPolynomial_weighted_spectralMeasure_eq_christoffelPolynomial hA b hk] using heq

end NLAlib
