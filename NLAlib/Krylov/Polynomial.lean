import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.LinearAlgebra.Matrix.ToLin
import NLAlib.Krylov.Basic

/-!
# Krylov subspaces: polynomial characterisation and basic structure

Facts about `NLAlib.krylovSpace A b q = span {b, A b, …, A^(q−1) b}`:

* `mem_krylovSpace_iff_degree`, `mem_krylovSpace_iff`: `K_q(A,b) = {p(A) b : deg p < q}`;
* `pow_mulVec_mem_krylovSpace`, `self_mem_krylovSpace_succ`: the generators lie in it;
* `krylovSpace_zero`, `krylovSpace_succ`: `K_0 = 0` and `K_{q+1} = K_q ⊔ span {A^q b}`;
* `krylovSpace_mono`: monotonicity in `q`;
* `mulVec_mem_krylovSpace_succ`: `A K_q ⊆ K_{q+1}`;
* `finrank_krylovSpace_le`: `dim K_q ≤ q`.

Source: Golub–Meurant (2010) [`gm10`], Ch. 4; Martinsson–Tropp (2020) [`mt20`], §11.7.
Atlas: `krylov-subspace`.
-/

noncomputable section

open scoped Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The generators `A^i b` (`i < q`) lie in `K_q(A,b)`. Atlas: `krylov-subspace`. -/
theorem pow_mulVec_mem_krylovSpace (A : Matrix n n ℝ) (b : n → ℝ) {q i : ℕ} (hi : i < q) :
    (A ^ i) *ᵥ b ∈ krylovSpace A b q :=
  Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

/-- `p(A) b` for a polynomial written in the monomial basis with coefficients `c : Fin q → ℝ`. -/
private lemma aeval_sum_fin_mulVec (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ} (c : Fin q → ℝ) :
    Polynomial.aeval A (∑ i : Fin q, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) *ᵥ b =
      ∑ i : Fin q, c i • ((A ^ (i : ℕ)) *ᵥ b) := by
  simp [map_sum, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

/-- Polynomial characterisation of the Krylov space, degree form (valid for every `q`, including
`q = 0` where both sides are `{0}`): `x ∈ K_q(A,b) ↔ x = p(A) b` for some `p` with `deg p < q`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 4; Martinsson–Tropp (2020) [`mt20`], §11.7.
Atlas: `krylov-subspace`.
atlas: krylov-subspace -/
theorem mem_krylovSpace_iff_degree (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) (x : n → ℝ) :
    x ∈ krylovSpace A b q ↔
      ∃ p : ℝ[X], p.degree < q ∧ x = Polynomial.aeval A p *ᵥ b := by
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
    exact ⟨_, Polynomial.degree_sum_fin_lt c, (aeval_sum_fin_mulVec A b c).symm⟩
  · rintro ⟨p, hp, rfl⟩
    by_cases hp0 : p = 0
    · subst hp0; simp
    have hnat : p.natDegree < q := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hp
    rw [p.as_sum_range' q hnat]
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => Polynomial.C (p.coeff i) * Polynomial.X ^ i), aeval_sum_fin_mulVec]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (pow_mulVec_mem_krylovSpace A b i.isLt)

/-- Polynomial characterisation of the Krylov space, `natDegree` form:
for `0 < q`, `x ∈ K_q(A,b) ↔ ∃ p, natDeg p < q ∧ x = p(A) b`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 4. Atlas: `krylov-subspace`.
Deviation: needs `0 < q` (for `q = 0` no polynomial has `natDegree < 0`; use
`mem_krylovSpace_iff_degree`).
atlas: krylov-subspace -/
theorem mem_krylovSpace_iff (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ} (hq : 0 < q) (x : n → ℝ) :
    x ∈ krylovSpace A b q ↔
      ∃ p : ℝ[X], p.natDegree < q ∧ x = Polynomial.aeval A p *ᵥ b := by
  rw [mem_krylovSpace_iff_degree]
  refine exists_congr fun p => and_congr_left fun _ => ?_
  by_cases hp0 : p = 0
  · subst hp0
    simp only [Polynomial.degree_zero, Polynomial.natDegree_zero, hq, iff_true]
    exact WithBot.bot_lt_coe q
  · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).symm

/-- The zeroth Krylov space is trivial: `K_0(A,b) = 0`. Atlas: `krylov-subspace`. -/
@[simp] theorem krylovSpace_zero (A : Matrix n n ℝ) (b : n → ℝ) : krylovSpace A b 0 = ⊥ := by
  rw [krylovSpace, Set.range_eq_empty, Submodule.span_empty]

/-- One Krylov step adds one generator: `K_{q+1}(A,b) = K_q(A,b) ⊔ span {A^q b}`.
Source: [`gm10`], Ch. 4. Atlas: `krylov-subspace`. -/
theorem krylovSpace_succ (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    krylovSpace A b (q + 1) = krylovSpace A b q ⊔ Submodule.span ℝ {(A ^ q) *ᵥ b} := by
  rw [krylovSpace, krylovSpace, ← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, rfl⟩
    · exact ⟨Fin.last q, rfl⟩

/-- Krylov spaces are nested: `q ≤ q' → K_q(A,b) ≤ K_{q'}(A,b)`. Source: [`gm10`], Ch. 4.
Atlas: `krylov-subspace`.
atlas: krylov-subspace -/
theorem krylovSpace_mono (A : Matrix n n ℝ) (b : n → ℝ) {q q' : ℕ} (h : q ≤ q') :
    krylovSpace A b q ≤ krylovSpace A b q' :=
  Submodule.span_le.2 <| by
    rintro _ ⟨i, rfl⟩
    exact pow_mulVec_mem_krylovSpace A b (lt_of_lt_of_le i.isLt h)

/-- `A K_q(A,b) ⊆ K_{q+1}(A,b)`. Source: [`gm10`], Ch. 4. Atlas: `krylov-subspace`.
atlas: krylov-subspace -/
theorem mulVec_mem_krylovSpace_succ (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ} {x : n → ℝ}
    (hx : x ∈ krylovSpace A b q) : A *ᵥ x ∈ krylovSpace A b (q + 1) := by
  have hle : krylovSpace A b q ≤ (krylovSpace A b (q + 1)).comap (Matrix.mulVecLin A) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change A *ᵥ ((A ^ (i : ℕ)) *ᵥ b) ∈ krylovSpace A b (q + 1)
    rw [Matrix.mulVec_mulVec, ← pow_succ']
    exact pow_mulVec_mem_krylovSpace A b (Nat.succ_lt_succ i.isLt)
  exact hle hx

/-- The starting vector lies in every nontrivial Krylov space: `b ∈ K_{q+1}(A,b)`.
Source: [`gm10`], Ch. 4. Atlas: `krylov-subspace`. -/
theorem self_mem_krylovSpace_succ (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    b ∈ krylovSpace A b (q + 1) := by
  simpa using pow_mulVec_mem_krylovSpace A b (Nat.succ_pos q)

/-- `dim K_q(A,b) ≤ q`. Source: [`gm10`], Ch. 4. Atlas: `krylov-subspace`.
atlas: krylov-subspace -/
theorem finrank_krylovSpace_le (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    Module.finrank ℝ (krylovSpace A b q) ≤ q := by
  exact (finrank_range_le_card (R := ℝ) (fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b)).trans
    (by simp)

end NLAlib
