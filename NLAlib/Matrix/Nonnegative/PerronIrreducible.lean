import NLAlib.Matrix.Nonnegative.PerronExistence
import NLAlib.Matrix.Spectral.EigenvalueSimplicity

/-! # Irreducible Perron eigenvectors and simplicity

Positive paths propagate a nonzero nonnegative eigenvector to every
coordinate. Subtracting the minimum multiple of a positive Perron vector
identifies the real eigenline. A positive left eigenvector excludes all
generalized eigenvectors, giving algebraic simplicity and the positive
rank-one spectral projector.
Source: Horn–Johnson, Matrix Analysis, Chapter 8.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- Irreducibility makes every nonzero nonnegative eigenvector strictly positive.
The eigenvalue need not be assumed positive in advance.
Source: Horn–Johnson, Chapter 8.
atlas: irreducible-perron-frobenius (partial) -/
theorem IsIrreducible.pos_of_nonnegative_eigenvector {A : Matrix ι ι ℝ}
    (hA : A.IsIrreducible) {p : ι → ℝ} {r : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpne : p ≠ 0) (heig : A *ᵥ p = r • p) :
    ∀ i, 0 < p i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hpne
  have hpj : 0 < p j := lt_of_le_of_ne (hp j) hj.symm
  intro i
  obtain ⟨k, hk, hki⟩ := (isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA i j
  have hpos : 0 < (A ^ k *ᵥ p) i := (mul_pos hki hpj).trans_le
    (Finset.single_le_sum (fun l _ => mul_nonneg (Matrix.pow_apply_nonneg hA.nonneg k i l) (hp l))
      (mem_univ j))
  by_contra hi
  have hz : p i = 0 := le_antisymm (le_of_not_gt hi) (hp i)
  rw [pow_mulVec_eq_pow_smul_of_mulVec_eq_smul heig, Pi.smul_apply, smul_eq_mul, hz, mul_zero] at hpos
  exact (lt_irrefl _ hpos)

/-- The real Perron eigenspace is exactly the line through any positive
Perron eigenvector. Reducibility is excluded by the zero-coordinate argument. -/
theorem IsIrreducible.eigenspace_eq_span_of_positive_eigenvector
    {A : Matrix ι ι ℝ} (hA : A.IsIrreducible) {p : ι → ℝ} {r : ℝ}
    (hp : ∀ i, 0 < p i) (heig : A *ᵥ p = r • p) :
    Module.End.eigenspace A.toLin' r = ℝ ∙ p := by
  apply le_antisymm
  · intro x hx
    have hxEig : A *ᵥ x = r • x := Module.End.mem_eigenspace_iff.mp hx
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (fun k => x k / p k)
      Finset.univ_nonempty
    let a := x i / p i
    let v := x - a • p
    have hv (j : ι) : 0 ≤ v j := sub_nonneg.mpr
      ((le_div_iff₀ (hp j)).mp (hi j (mem_univ j)))
    have hvi : v i = 0 := by
      dsimp [v, a]
      field_simp [(hp i).ne']
      ring
    have hvEig : A *ᵥ v = r • v := by
      simp only [v, Matrix.mulVec_sub, Matrix.mulVec_smul, hxEig, heig, smul_sub, smul_smul]
      rw [mul_comm r a]
    have hv0 : v = 0 := by
      by_contra hne
      have hpos := hA.pos_of_nonnegative_eigenvector hv hne hvEig i
      rw [hvi] at hpos
      exact (lt_irrefl _ hpos)
    exact Submodule.mem_span_singleton.mpr ⟨a, (sub_eq_zero.mp hv0).symm⟩
  · apply (Submodule.span_singleton_le_iff_mem p _).mpr
    exact Module.End.mem_eigenspace_iff.mpr heig

/-- Left and right nonnegative unit-sum Perron vectors are strictly positive
for a nonzero irreducible matrix, and its spectral radius is strictly positive.
Source: Horn–Johnson, Chapter 8.
atlas: irreducible-perron-frobenius (partial) -/
theorem IsIrreducible.exists_positive_perron_pair {A : Matrix ι ι ℝ}
    (hA : A.IsIrreducible) (hAne : A ≠ 0) :
    ∃ p q : ι → ℝ,
      0 < (spectralRadius ℂ (A.map Complex.ofReal)).toReal ∧
      (∀ i, 0 < p i) ∧ (∀ i, 0 < q i) ∧ (∑ i, p i = 1) ∧ (∑ i, q i = 1) ∧
      A *ᵥ p = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • p ∧
      q ᵥ* A = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • q := by
  obtain ⟨p, hp, hpsum, heig⟩ := exists_nonnegative_perron_eigenvector hA.nonneg
  obtain ⟨q, hq, hqsum, hqeig⟩ := exists_nonnegative_perron_eigenvector hA.transpose.nonneg
  have hspec : spectrum ℂ (Aᵀ.map Complex.ofReal) = spectrum ℂ (A.map Complex.ofReal) := by
    ext μ
    change μ ∈ spectrum ℂ (A.map Complex.ofReal)ᵀ ↔ _
    simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose]
  have hradii : spectralRadius ℂ (Aᵀ.map Complex.ofReal) =
      spectralRadius ℂ (A.map Complex.ofReal) := by simp only [spectralRadius, hspec]
  rw [hradii] at hqeig
  have hpne : p ≠ 0 := by intro hz; simp [hz] at hpsum
  have hqne : q ≠ 0 := by intro hz; simp [hz] at hqsum
  have hpp := hA.pos_of_nonnegative_eigenvector hp hpne heig
  have hqq := hA.transpose.pos_of_nonnegative_eigenvector hq hqne hqeig
  have hentry : ∃ i j, A i j ≠ 0 := by
    by_contra! h
    exact hAne (funext fun i => funext fun j => h i j)
  obtain ⟨i, j, hij⟩ := hentry
  have hpos : 0 < (A *ᵥ p) i :=
    (mul_pos (lt_of_le_of_ne (hA.nonneg i j) hij.symm) (hpp j)).trans_le
      (Finset.single_le_sum (fun k _ => mul_nonneg (hA.nonneg i k) (hp k)) (mem_univ j))
  have hrpos : 0 < (spectralRadius ℂ (A.map Complex.ofReal)).toReal := by
    rw [heig] at hpos
    exact (mul_pos_iff_of_pos_right (hpp i)).mp hpos
  exact ⟨p, q, hrpos, hpp, hqq, hpsum, hqsum, heig, by
    simpa only [Matrix.mulVec_transpose] using hqeig⟩

/-- The Perron root of a nonzero irreducible matrix has algebraic multiplicity
one; positivity of the left–right pairing rules out generalized eigenvectors.
Source: Horn–Johnson, Chapter 8.
atlas: irreducible-perron-frobenius (partial) -/
theorem IsIrreducible.rootMultiplicity_perron_eq_one {A : Matrix ι ι ℝ}
    (hA : A.IsIrreducible) (hAne : A ≠ 0) :
    A.charpoly.rootMultiplicity (spectralRadius ℂ (A.map Complex.ofReal)).toReal = 1 := by
  obtain ⟨p, q, _, hp, hq, _, _, hAp, hqA⟩ := hA.exists_positive_perron_pair hAne
  have hpne : p ≠ 0 := by
    intro hz
    have h := hp (Classical.choice ‹Nonempty ι›)
    rw [hz] at h
    exact lt_irrefl _ h
  have hdim : Module.finrank ℝ (Module.End.eigenspace A.toLin'
      (spectralRadius ℂ (A.map Complex.ofReal)).toReal) = 1 := by
    rw [hA.eigenspace_eq_span_of_positive_eigenvector hp hAp, finrank_span_singleton hpne]
  have hpair : 0 < q ⬝ᵥ p := Finset.sum_pos (fun i _ => mul_pos (hq i) (hp i)) Finset.univ_nonempty
  exact NLAlib.rootMultiplicity_eq_one_of_finrank_eigenspace_eq_one_of_pairing_ne_zero
    hAp hqA hdim hpair.ne'

/-- Algebraic simplicity is also stated directly for the complexification.
Source: Horn–Johnson, Chapter 8.
atlas: irreducible-perron-frobenius (partial) -/
theorem IsIrreducible.rootMultiplicity_perron_complexification_eq_one
    {A : Matrix ι ι ℝ} (hA : A.IsIrreducible) (hAne : A ≠ 0) :
    (A.map Complex.ofReal).charpoly.rootMultiplicity
      ((spectralRadius ℂ (A.map Complex.ofReal)).toReal : ℂ) = 1 := by
  have hmap : (A.map Complex.ofReal).charpoly = A.charpoly.map Complex.ofRealHom :=
    Matrix.charpoly_map A Complex.ofRealHom
  rw [hmap]
  have hroot := Polynomial.eq_rootMultiplicity_map (p := A.charpoly) (f := Complex.ofRealHom)
    Complex.ofReal_injective (spectralRadius ℂ (A.map Complex.ofReal)).toReal
  exact hroot.symm.trans (hA.rootMultiplicity_perron_eq_one hAne)

/-- Every nonzero nonnegative eigenvector of an irreducible matrix is a
positive multiple of a specified positive Perron vector. Its eigenvalue is
necessarily the Perron root.
Source: Horn–Johnson, Chapter 8.
atlas: irreducible-perron-frobenius (partial) -/
theorem IsIrreducible.nonnegative_eigenvector_eq_pos_smul
    {A : Matrix ι ι ℝ} (hA : A.IsIrreducible) (hAne : A ≠ 0)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (hAp : A *ᵥ p = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • p)
    {v : ι → ℝ} {μ : ℝ} (hv : ∀ i, 0 ≤ v i) (hvne : v ≠ 0)
    (hAv : A *ᵥ v = μ • v) :
    μ = (spectralRadius ℂ (A.map Complex.ofReal)).toReal ∧ ∃ c : ℝ, 0 < c ∧ v = c • p := by
  obtain ⟨_, q, _, _, hq, _, _, _, hqA⟩ := hA.exists_positive_perron_pair hAne
  have hvpos := hA.pos_of_nonnegative_eigenvector hv hvne hAv
  have hpair : 0 < q ⬝ᵥ v := Finset.sum_pos (fun i _ => mul_pos (hq i) (hvpos i)) Finset.univ_nonempty
  have heq : μ * (q ⬝ᵥ v) = (spectralRadius ℂ (A.map Complex.ofReal)).toReal * (q ⬝ᵥ v) := by
    calc
      _ = q ⬝ᵥ (A *ᵥ v) := by rw [hAv, dotProduct_smul]; rfl
      _ = (q ᵥ* A) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = _ := by rw [hqA, smul_dotProduct]; rfl
  have hμ := (mul_right_cancel₀ hpair.ne') heq
  refine ⟨hμ, ?_⟩
  have hmem : v ∈ Module.End.eigenspace A.toLin'
      (spectralRadius ℂ (A.map Complex.ofReal)).toReal :=
    Module.End.mem_eigenspace_iff.mpr (by
      change A *ᵥ v = _
      rw [hAv, hμ])
  rw [hA.eigenspace_eq_span_of_positive_eigenvector hp hAp] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcpos : 0 < c := by
    let i : ι := Classical.choice ‹Nonempty ι›
    have hvi := hvpos i
    rw [← hc] at hvi
    exact (mul_pos_iff_of_pos_right (hp i)).mp hvi
  exact ⟨c, hcpos, hc.symm⟩

omit [DecidableEq ι] in
/-- The normalized left–right Perron projector is strictly positive,
idempotent, and commutes with the matrix at the Perron root. The formula is
oblique in general; no symmetry is asserted.
Source: Horn–Johnson, Chapter 8.
atlas: irreducible-perron-frobenius (partial) -/
theorem perron_projector_pos_idempotent_and_commutes
    {A : Matrix ι ι ℝ} {p q : ι → ℝ} {r : ℝ}
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hAp : A *ᵥ p = r • p) (hqA : q ᵥ* A = r • q) :
    let P := (q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q
    (∀ i j, 0 < P i j) ∧ P * P = P ∧ A * P = r • P ∧ P * A = r • P := by
  have hpair : 0 < q ⬝ᵥ p := Finset.sum_pos (fun i _ => mul_pos (hq i) (hp i)) Finset.univ_nonempty
  refine ⟨fun i j => ?_, NLAlib.normalized_vecMulVec_mul_self hpair.ne',
    NLAlib.mul_normalized_vecMulVec_eq_smul hAp hqA⟩
  exact mul_pos (inv_pos.mpr hpair) (mul_pos (hp i) (hq j))

end Matrix
