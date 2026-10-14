import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Bounded-degree partial fractions with repeated linear poles

Mathlib's native finite partial-fraction decomposition is specialized to linear
factors. The polynomial and principal-part coefficients are unique, and the
polynomial degree bound is exactly the numerator bound minus the pole degree.
-/

noncomputable section
open Polynomial Finset
namespace Polynomial
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

/-- The monic denominator with the displayed repeated linear poles. -/
def linearPoleProduct (v : ι → 𝕜) (s : ι → ℕ) : 𝕜[X] :=
  ∏ i, (X-C (v i))^(s i)

/-- Clearing the denominator of the principal parts gives this polynomial.
Index `j` represents the pole power `s i-j`, so every power from one to `s i`
is included once. -/
def linearPoleRemainder (v : ι → 𝕜) (s : ι → ℕ)
    (c : (i : ι) → Fin (s i) → 𝕜) : 𝕜[X] :=
  ∑ i, ∑ j : Fin (s i), C (c i j) * (X-C (v i))^j.val *
    ∏ k ∈ univ.erase i, (X-C (v k))^(s k)

omit [DecidableEq ι] in
/-- The repeated-pole product is monic, including the empty product. -/
theorem monic_linearPoleProduct (v : ι → 𝕜) (s : ι → ℕ) :
    (linearPoleProduct v s).Monic := monic_prod_of_monic _ _
      (fun i _ => (monic_X_sub_C (v i)).pow (s i))

omit [DecidableEq ι] in
/-- The denominator degree is exactly the sum of the pole multiplicities. -/
@[simp] theorem natDegree_linearPoleProduct (v : ι → 𝕜) (s : ι → ℕ) :
    (linearPoleProduct v s).natDegree = ∑ i, s i := by
  rw [linearPoleProduct, natDegree_prod_of_monic _ _
    (fun i _ => (monic_X_sub_C (v i)).pow (s i))]
  simp

/-- Every cleared principal-part numerator has degree strictly below the
full denominator degree, even when there are no poles. -/
theorem degree_linearPoleRemainder_lt (v : ι → 𝕜) (s : ι → ℕ)
    (c : (i : ι) → Fin (s i) → 𝕜) :
    (linearPoleRemainder v s c).degree < (∑ i, s i : ℕ) := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro i _
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro j _
  have hprod : (∏ k ∈ univ.erase i, (X-C (v k))^(s k)).degree =
      ((∑ k ∈ univ.erase i, s k : ℕ) : WithBot ℕ) := by
    rw [degree_prod_of_monic _ _ (fun k _ => (monic_X_sub_C (v k)).pow (s k))]
    simp
  have hsum : s i + (∑ k ∈ univ.erase i, s k) = ∑ k, s k :=
    (add_comm _ _).trans (sum_erase_add _ _ (mem_univ i))
  have hdeg : (C (c i j) * (X-C (v i))^j.val *
      ∏ k ∈ univ.erase i, (X-C (v k))^(s k)).degree ≤
        ((j.val + (∑ k ∈ univ.erase i, s k) : ℕ) : WithBot ℕ) := by
    apply (degree_mul_le _ _).trans
    rw [hprod, Nat.cast_add]
    apply add_le_add _ le_rfl
    apply (degree_mul_le _ _).trans
    simp only [degree_pow, degree_X_sub_C, nsmul_eq_mul, mul_one]
    simpa only [zero_add] using add_le_add (degree_C_le (a := c i j))
      (le_refl (j.val : WithBot ℕ))
  exact hdeg.trans_lt (by exact_mod_cast (show j.val + (∑ k ∈ univ.erase i, s k) < ∑ k, s k by omega))

private theorem eq_C_of_degree_lt_one {p : 𝕜[X]} (hp : p.degree < (1 : WithBot ℕ)) :
    p = C (p.coeff 0) := by
  by_cases h0 : p = 0
  · simp [h0]
  rw [degree_eq_natDegree h0] at hp
  apply eq_C_of_natDegree_eq_zero
  have h : p.natDegree < 1 := by exact_mod_cast hp
  omega

/-- Every polynomial has a unique polynomial-plus-principal-part expansion
after clearing the actual repeated-pole denominator. This is directness of
the rational-space sum; it includes repeated poles and an empty pole family. -/
theorem existsUnique_eq_mul_linearPoleProduct_add_linearPoleRemainder
    (v : ι → 𝕜) (hv : Function.Injective v) (s : ι → ℕ) (p : 𝕜[X]) :
    ∃! qc : 𝕜[X] × ((i : ι) → Fin (s i) → 𝕜),
      p = qc.1 * linearPoleProduct v s + linearPoleRemainder v s qc.2 := by
  have hcop : Set.Pairwise (univ : Finset ι) (fun i j =>
      IsCoprime (X-C (v i)) (X-C (v j))) := fun i _ j _ hij => pairwise_coprime_X_sub_C hv hij
  obtain ⟨q, r, hr, he⟩ := eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow p
    (fun i _ => monic_X_sub_C (v i)) hcop s
  let c : (i : ι) → Fin (s i) → 𝕜 := fun i j => (r i j).coeff 0
  have hrc (i : ι) (j : Fin (s i)) : r i j = C (c i j) :=
    eq_C_of_degree_lt_one (by simpa only [degree_X_sub_C] using hr i (mem_univ i) j)
  have heq : p = q * linearPoleProduct v s + linearPoleRemainder v s c := by
    simpa only [linearPoleProduct, linearPoleRemainder, hrc] using he
  refine ⟨(q,c), heq, ?_⟩
  rintro ⟨q',c'⟩ he'
  obtain ⟨hq, hc⟩ := quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique
    (fun i _ => monic_X_sub_C (v i)) hcop
    (q₁ := q') (q₂ := q) (r₁ := fun i j => C (c' i j)) (r₂ := fun i j => C (c i j))
    (fun i _ j => (degree_C_le).trans_lt (by simp))
    (fun i _ j => (degree_C_le).trans_lt (by simp)) (he'.symm.trans heq)
  refine Prod.ext hq ?_
  funext i j
  have h := congrArg (fun r => (r j).coeff 0) (hc i (mem_univ i))
  simpa only [coeff_C_zero] using h

/-- The bounded numerator space has exactly the advertised polynomial degree
bound in its unique partial-fraction expansion. When the pole degree equals
`d`, the polynomial part is necessarily zero (`degree < 0`). -/
theorem degree_mul_linearPoleProduct_add_linearPoleRemainder_lt_iff
    (v : ι → 𝕜) (s : ι → ℕ) {d : ℕ} (hmd : (∑ i, s i) ≤ d)
    (q : 𝕜[X]) (c : (i : ι) → Fin (s i) → 𝕜) :
    (q * linearPoleProduct v s + linearPoleRemainder v s c).degree < d ↔
      q.degree < (d - ∑ i, s i : ℕ) := by
  by_cases hq : q = 0
  · rw [hq, zero_mul, zero_add, degree_zero]
    constructor
    · intro _
      exact WithBot.bot_lt_coe _
    · intro _
      exact (degree_linearPoleRemainder_lt v s c).trans_le
        (show (∑ i, s i : ℕ) ≤ (d : WithBot ℕ) by exact_mod_cast hmd)
  have hqdeg : q.degree = (q.natDegree : ℕ) := degree_eq_natDegree hq
  have hprod : (linearPoleProduct v s).degree = (∑ i, s i : ℕ) := by
    rw [degree_eq_natDegree (monic_linearPoleProduct v s).ne_zero, natDegree_linearPoleProduct]
  have hsmall : (linearPoleRemainder v s c).degree < (q * linearPoleProduct v s).degree := by
    rw [degree_mul, hqdeg, hprod, ← Nat.cast_add]
    exact (degree_linearPoleRemainder_lt v s c).trans_le (by exact_mod_cast Nat.le_add_left _ _)
  rw [degree_add_eq_left_of_degree_lt hsmall, degree_mul, hqdeg, hprod, ← Nat.cast_add]
  norm_cast
  omega

end Polynomial
