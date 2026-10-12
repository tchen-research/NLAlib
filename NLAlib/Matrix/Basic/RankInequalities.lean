import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Rank inequalities and affine solution sets

Restriction of a linear map to a subspace proves Sylvester's and Frobenius's
rank inequalities. Horn–Johnson 2013, §§0.4.2 and 0.4.5;
atlas `rank-inequalities`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E]

/-- Rank-nullity on a subspace says that the image dimension plus the
dimension lost in the kernel is the original dimension. Horn–Johnson §0.4.2;
helper for `rank-inequalities`. -/
theorem finrank_map_add_finrank_inf_ker (f : E →ₗ[K] F) (S : Submodule K E) :
    Module.finrank K (S.map f) + Module.finrank K (S ⊓ LinearMap.ker f : Submodule K E) =
      Module.finrank K S := by
  let e : LinearMap.ker (f.domRestrict S) ≃ₗ[K] (S ⊓ LinearMap.ker f : Submodule K E) :=
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := (f.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, e.finrank_eq] at h
  exact h

variable {m n p q : Type*} [Fintype n] [Fintype p] [Fintype q]

/-- Sylvester's rank inequality with natural-number subtraction, including
empty indices. Horn–Johnson 2013, §0.4.2.
atlas: rank-inequalities -/
theorem rank_add_rank_sub_card_le_rank_mul (A : Matrix m n K) (B : Matrix n p K) :
    A.rank + B.rank - Fintype.card n ≤ (A * B).rank := by
  have hB := finrank_map_add_finrank_inf_ker A.mulVecLin (LinearMap.range B.mulVecLin)
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hle : Module.finrank K (LinearMap.range B.mulVecLin ⊓ LinearMap.ker A.mulVecLin :
      Submodule K (n → K)) ≤ Module.finrank K (LinearMap.ker A.mulVecLin) :=
    Submodule.finrank_mono inf_le_right
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul] at hB
  rw [Module.finrank_pi] at hA
  change (A * B).rank + _ = B.rank at hB
  change A.rank + _ = Fintype.card n at hA
  omega

/-- Frobenius's rank inequality for three conformable matrices over a field,
including empty indices. Horn–Johnson 2013, §0.4.2.
atlas: rank-inequalities -/
theorem rank_mul_add_rank_mul_le_rank_add_rank_mul_mul
    (A : Matrix m n K) (B : Matrix n p K) (C : Matrix p q K) :
    (A * B).rank + (B * C).rank ≤ B.rank + (A * B * C).rank := by
  have hB := finrank_map_add_finrank_inf_ker A.mulVecLin (LinearMap.range B.mulVecLin)
  have hBC := finrank_map_add_finrank_inf_ker A.mulVecLin
    (LinearMap.range (B * C).mulVecLin)
  have hRange : LinearMap.range (B * C).mulVecLin ≤ LinearMap.range B.mulVecLin := by
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hle := Submodule.finrank_mono (inf_le_inf_right (LinearMap.ker A.mulVecLin) hRange)
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul] at hB hBC
  change (A * B).rank + _ = B.rank at hB
  change (A * (B * C)).rank + _ = (B * C).rank at hBC
  rw [← Matrix.mul_assoc] at hBC
  omega

/-- Once one solution is given, all solutions differ from it by a vector
in the matrix kernel. Horn–Johnson 2013, §0.4.5.
atlas: rank-inequalities -/
theorem mulVec_eq_iff_sub_mem_ker (A : Matrix m n K) (b : m → K) (x₀ : n → K)
    (h₀ : A *ᵥ x₀ = b) (x : n → K) :
    A *ᵥ x = b ↔ x - x₀ ∈ LinearMap.ker A.mulVecLin := by
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, h₀,
    sub_eq_zero]

/-- The full rank bounds for a product, including the Sylvester lower bound,
hold over arbitrary fields and finite middle/column indices. Horn–Johnson
2013, §0.4.2.
atlas: rank-inequalities -/
theorem rank_mul_bounds (A : Matrix m n K) (B : Matrix n p K) :
    A.rank + B.rank - Fintype.card n ≤ (A * B).rank ∧
      (A * B).rank ≤ min A.rank B.rank :=
  ⟨rank_add_rank_sub_card_le_rank_mul A B, Matrix.rank_mul_le A B⟩

/-- Adjoining a column does not increase rank exactly when that column lies
in the original column space. This is the Rouché–Capelli solvability criterion,
with arbitrary finite indices and all zero-dimensional cases.
Horn–Johnson 2013, §0.4.5.
atlas: rank-inequalities -/
theorem rank_fromCols_eq_iff_exists_mulVec_eq [Fintype m]
    (A : Matrix m n K) (b : m → K) :
    (Matrix.fromCols A (fun i (_ : Unit) => b i)).rank = A.rank ↔
      ∃ x : n → K, A *ᵥ x = b := by
  let S := Submodule.span K (Set.range A.col)
  have hCols : Set.range (Matrix.fromCols A (fun i (_ : Unit) => b i)).col =
      Set.range A.col ∪ {b} := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr j => exact Or.inr rfl
    · rintro (⟨j, rfl⟩ | rfl)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr (), rfl⟩
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols,
    hCols, Submodule.span_union]
  change Module.finrank K (S ⊔ Submodule.span K {b} : Submodule K (m → K)) =
    Module.finrank K S ↔ _
  constructor
  · intro h
    have hEq : S = S ⊔ Submodule.span K {b} :=
      Submodule.eq_of_le_of_finrank_eq le_sup_left h.symm
    have hb : b ∈ S := by
      rw [hEq]
      exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton b))
    change b ∈ Submodule.span K (Set.range A.col) at hb
    rw [← Matrix.range_mulVecLin] at hb
    exact hb
  · rintro ⟨x, hx⟩
    have hb : b ∈ S := by
      change b ∈ Submodule.span K (Set.range A.col)
      rw [← Matrix.range_mulVecLin]
      exact ⟨x, hx⟩
    rw [sup_eq_left.mpr (Submodule.span_le.mpr (by simpa using hb))]

/-- The affine solution set is the translate of the kernel through any one
solution. Horn–Johnson 2013, §0.4.5.
atlas: rank-inequalities -/
theorem solution_set_eq_add_ker (A : Matrix m n K) (b : m → K) (x₀ : n → K)
    (h₀ : A *ᵥ x₀ = b) :
    {x : n → K | A *ᵥ x = b} =
      {x : n → K | ∃ z ∈ LinearMap.ker A.mulVecLin, x = x₀ + z} := by
  ext x
  change (A *ᵥ x = b) ↔ ∃ z ∈ LinearMap.ker A.mulVecLin, x = x₀ + z
  constructor
  · intro hx
    refine ⟨x - x₀, (mulVec_eq_iff_sub_mem_ker A b x₀ h₀ x).mp hx, ?_⟩
    abel
  · rintro ⟨z, hz, rfl⟩
    rw [Matrix.mulVec_add, h₀, show A *ᵥ z = 0 from hz, add_zero]

end NLAlib
