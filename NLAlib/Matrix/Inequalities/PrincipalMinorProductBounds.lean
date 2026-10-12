import NLAlib.Matrix.Inequalities.PrincipalMinorProducts
import NLAlib.ForMathlib.Combinatorics.SubsetDeletionProduct
import NLAlib.Matrix.Inequalities.InverseDiagonalMinor
/-!
# Products of consecutive principal-minor orders

Inverse Hadamard gives the local deletion inequality; counting its product
over all coordinate sets gives Szász's integer-power form. Strictness detects
every off-diagonal entry by a containing coordinate set.
Source: Horn--Johnson (2013), Lemma 7.8.8 and Theorem 7.8.11;
atlas `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- The local one-element-deletion inequality and exact equality inside
each nonempty principal block. Horn--Johnson (2013), Lemma 7.8.8;
helper for Szász's inequality. -/
theorem principalMinor_pow_pred_le_prod_erase_and_eq_iff {A : Matrix n n ℝ}
    (hA : A.PosDef) (T : Finset n) (hT : T.Nonempty) :
    principalMinor A T ^ (T.card - 1) ≤ ∏ i ∈ T, principalMinor A (T.erase i) ∧
    (principalMinor A T ^ (T.card - 1) = (∏ i ∈ T, principalMinor A (T.erase i)) ↔
      (A.toBlock (· ∈ T) (· ∈ T)).IsDiag) := by
  let : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  have hM : (A.toBlock (· ∈ T) (· ∈ T)).PosDef := hA.submatrix Subtype.val_injective
  have h := det_pow_card_pred_le_prod_complement_singleton_and_eq_iff hM
  simp only [Fintype.card_coe, det_toBlock_complement_eq_principalMinor_erase] at h
  have hp : (∏ i : T, principalMinor A (T.erase i.val)) = ∏ i ∈ T, principalMinor A (T.erase i) :=
    Finset.prod_coe_sort T (fun i => principalMinor A (T.erase i))
  rw [hp] at h
  exact h

/-- The product at order `k+1`, raised to `k`, is bounded by the product at
order `k`, raised to `card n-k`. The integer-power form is valid at all
natural indices, including its vacuous endpoint and out-of-range cases.
Horn--Johnson (2013), proof of Theorem 7.8.11;
helper for normalized Szász products. -/
theorem principalMinorProduct_succ_pow_le_of_posDef {A : Matrix n n ℝ}
    (hA : A.PosDef) (k : ℕ) :
    principalMinorProduct A (k + 1) ^ k ≤ principalMinorProduct A k ^ (Fintype.card n - k) := by
  have hlocal (T : Finset n) (hT : T ∈ (Finset.univ : Finset n).powersetCard (k + 1)) :
      principalMinor A T ^ k ≤ ∏ i ∈ T, principalMinor A (T.erase i) := by
    have hc := (Finset.mem_powersetCard.mp hT).2
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    simpa only [hc, Nat.add_sub_cancel] using (principalMinor_pow_pred_le_prod_erase_and_eq_iff hA T hne).1
  have hp := Finset.prod_le_prod
    (s := (Finset.univ : Finset n).powersetCard (k + 1))
    (fun T _ => pow_nonneg (principalMinor_pos hA T).le k) hlocal
  rw [Finset.prod_pow, prod_powersetCard_prod_erase_eq_pow] at hp
  exact hp

/-- The integer-power Szász inequality holds throughout the PSD cone,
including singular matrices, by continuity of principal-minor products.
Horn--Johnson (2013), Theorem 7.8.11 and semidefinite extension.
atlas: hadamard-fischer-inequalities (partial) -/
theorem principalMinorProduct_succ_pow_le_of_posSemidef {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (k : ℕ) :
    principalMinorProduct A (k + 1) ^ k ≤ principalMinorProduct A k ^ (Fintype.card n - k) :=
  le_of_posSemidef_of_continuous_of_forall_posDef (by fun_prop) (by fun_prop)
    (fun M hM => principalMinorProduct_succ_pow_le_of_posDef hM k) hA

/-- Equality between consecutive principal-minor product powers for a
positive definite matrix holds exactly when the entire matrix is diagonal.
The index conditions exclude comparisons that are automatically equal.
Horn--Johnson (2013), Theorem 7.8.11.
atlas: hadamard-fischer-inequalities (partial) -/
theorem principalMinorProduct_succ_pow_eq_iff_isDiag {A : Matrix n n ℝ}
    (hA : A.PosDef) {k : ℕ} (hk : 1 ≤ k) (hkn : k < Fintype.card n) :
    principalMinorProduct A (k + 1) ^ k = principalMinorProduct A k ^ (Fintype.card n - k) ↔ A.IsDiag := by
  classical
  have hlocal (T : Finset n) (hT : T ∈ (Finset.univ : Finset n).powersetCard (k + 1)) :
      principalMinor A T ^ k ≤ ∏ i ∈ T, principalMinor A (T.erase i) ∧
      (principalMinor A T ^ k = (∏ i ∈ T, principalMinor A (T.erase i)) ↔
        (A.toBlock (· ∈ T) (· ∈ T)).IsDiag) := by
    have hc := (Finset.mem_powersetCard.mp hT).2
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    simpa only [hc, Nat.add_sub_cancel] using principalMinor_pow_pred_le_prod_erase_and_eq_iff hA T hne
  constructor
  · intro heq
    have hAll (T : Finset n) (hT : T ∈ (Finset.univ : Finset n).powersetCard (k + 1)) :
        (A.toBlock (· ∈ T) (· ∈ T)).IsDiag := by
      by_contra hnot
      have hlt : principalMinor A T ^ k < ∏ i ∈ T, principalMinor A (T.erase i) :=
        lt_of_le_of_ne (hlocal T hT).1 (fun h => hnot ((hlocal T hT).2.mp h))
      have hp := Finset.prod_lt_prod
        (s := (Finset.univ : Finset n).powersetCard (k + 1))
        (fun S _ => pow_pos (principalMinor_pos hA S) k)
        (fun S hS => (hlocal S hS).1) ⟨T, hT, hlt⟩
      rw [Finset.prod_pow, prod_powersetCard_prod_erase_eq_pow] at hp
      exact (ne_of_lt hp) heq
    intro i j hij
    obtain ⟨T, hpair, -, hcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ ({i, j} : Finset n))
      (show ({i, j} : Finset n).card ≤ k + 1 by simp [hij]; omega)
      (show k + 1 ≤ (Finset.univ : Finset n).card by simpa using hkn)
    have hT : T ∈ (Finset.univ : Finset n).powersetCard (k + 1) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    exact hAll T hT (i := ⟨i, hpair (by simp)⟩) (j := ⟨j, hpair (by simp)⟩)
      (fun h => hij (congrArg Subtype.val h))
  · intro hDiag
    have hp : (∏ T ∈ (Finset.univ : Finset n).powersetCard (k + 1), principalMinor A T ^ k) =
        ∏ T ∈ (Finset.univ : Finset n).powersetCard (k + 1), ∏ i ∈ T, principalMinor A (T.erase i) := by
      apply Finset.prod_congr rfl
      intro T hT
      exact (hlocal T hT).2.mpr (hDiag.submatrix Subtype.val_injective)
    rw [Finset.prod_pow, prod_powersetCard_prod_erase_eq_pow] at hp
    exact hp

end NLAlib
