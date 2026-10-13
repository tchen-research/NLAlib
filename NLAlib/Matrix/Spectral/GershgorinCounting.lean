import NLAlib.Matrix.Spectral.GershgorinBasic
import NLAlib.Matrix.Spectral.SpectrumCountContinuity

/-!
# Exact Gershgorin counts in isolated unions

The diagonal-to-matrix homotopy keeps each row disc inside its original disc.
Compact root-count fibers are constant on the parameter interval. The count
at the diagonal matrix is the number of selected centers, with multiplicity.
Source: Horn–Johnson (2013), Theorem 6.1.1 and Corollary 6.1.3.
-/

noncomputable section
open Polynomial
open scoped Matrix Topology Classical

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A union of `|I|` closed row discs, disjoint from the remaining closed
row discs, contains exactly `|I|` eigenvalues with algebraic multiplicity.
Source: Horn–Johnson (2013), Theorem 6.1.1; internal overlaps, repeated roots,
zero-radius discs, empty selections and empty matrices are included.
atlas: gershgorin-diagonal-dominance -/
theorem charpolyRootCountIn_gershgorinRowUnion_eq_card
    (A : Matrix n n ℂ) (I : Finset n)
    (hdisj : Disjoint (gershgorinRowUnion A I) (gershgorinRowUnion A Iᶜ)) :
    charpolyRootCountIn A (gershgorinRowUnion A I) = I.card := by
  let Ω := Set.Icc (0 : ℝ) 1
  let : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let H : Ω → Matrix n n ℂ := fun t =>
    Matrix.diagonal A.diag + (t.val : ℂ) • (A - Matrix.diagonal A.diag)
  have hH : Continuous H := by fun_prop
  have hdiag (t : Ω) (i : n) : H t i i = A i i := by
    simp only [H, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.diagonal_apply_eq, Matrix.diag_apply, sub_self, smul_zero, add_zero]
  have hradius (t : Ω) (i : n) : gershgorinRowRadius (H t) i = t.val * gershgorinRowRadius A i := by
    dsimp only [gershgorinRowRadius]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    simp only [H, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.diagonal_apply_ne _ hij, zero_add, sub_zero, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  have hspec (t : Ω) : spectrum ℂ (H t) ⊆ gershgorinRowUnion A I ∪ gershgorinRowUnion A Iᶜ := by
    intro μ hμ
    obtain ⟨i, hi⟩ := exists_mem_gershgorinRowDisc_of_mem_spectrum hμ
    have hmem : μ ∈ gershgorinRowDisc A i := by
      change dist μ (H t i i) ≤ gershgorinRowRadius (H t) i at hi
      rw [hdiag, hradius] at hi
      exact hi.trans (mul_le_of_le_one_left (gershgorinRowRadius_nonneg A i) t.property.2)
    by_cases hiI : i ∈ I
    · exact Or.inl (mem_gershgorinRowUnion_of_mem hiI hmem)
    · exact Or.inr (mem_gershgorinRowUnion_of_mem (Finset.mem_compl.mpr hiI) hmem)
  let t₀ : Ω := ⟨0, by constructor <;> norm_num⟩
  let t₁ : Ω := ⟨1, by constructor <;> norm_num⟩
  have hH₀ : H t₀ = Matrix.diagonal A.diag := by simp [H, t₀]
  have hH₁ : H t₁ = A := by simp [H, t₁]
  have hcount := charpolyRootCountIn_eq_of_preconnected H hH
    (gershgorinRowUnion A I) (gershgorinRowUnion A Iᶜ)
    (isCompact_gershgorinRowUnion A I) (isCompact_gershgorinRowUnion A Iᶜ) hdisj hspec t₁ t₀
  rw [hH₁, hH₀] at hcount
  rw [hcount, charpolyRootCountIn_eq_card_filter _ _ A.diag (Matrix.charpoly_diagonal A.diag)]
  have hfilter : Finset.univ.filter (fun i : n => A.diag i ∈ gershgorinRowUnion A I) = I := by
    apply Finset.ext
    intro i
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Matrix.diag_apply]
    constructor
    · intro hi
      by_contra hiI
      have hL : A i i ∈ gershgorinRowUnion A Iᶜ :=
        mem_gershgorinRowUnion_of_mem (Finset.mem_compl.mpr hiI) (diagonal_mem_gershgorinRowDisc A i)
      exact Set.disjoint_left.mp hdisj hi hL
    · intro hi
      exact mem_gershgorinRowUnion_of_mem hi (diagonal_mem_gershgorinRowDisc A i)
  rw [hfilter]

/-- A union of selected closed column discs, disjoint from the remaining
closed column discs, contains exactly as many algebraic eigenvalues as
selected columns. Source: Horn–Johnson (2013), Corollary 6.1.3; all degenerate
and repeated-root cases are retained by transpose and the root multiset.
atlas: gershgorin-diagonal-dominance -/
theorem charpolyRootCountIn_gershgorinColumnUnion_eq_card
    (A : Matrix n n ℂ) (I : Finset n)
    (hdisj : Disjoint (gershgorinColumnUnion A I) (gershgorinColumnUnion A Iᶜ)) :
    charpolyRootCountIn A (gershgorinColumnUnion A I) = I.card := by
  have h := charpolyRootCountIn_gershgorinRowUnion_eq_card Aᵀ I hdisj
  unfold charpolyRootCountIn at h ⊢
  rw [Matrix.charpoly_transpose] at h
  exact h

end NLAlib
