import NLAlib.Gaussian.PolynomialLinearMoments
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange

/-!
# The finite canonical pairing family and Gaussian Wick evaluation

A pairing matches the first remaining position with its unique partner and
recursively pairs the remaining positions. This is a finite data type, not a
moment or Stein hypothesis. Odd families are empty and the empty family has
the single empty pairing. Source: operator re-derivation `pg:wick`.
Supports atlas `isserlis`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- All unordered complete pairings of `m` labelled positions, in canonical
order: choose the partner of the smallest remaining position, then recurse.
Source: Isserlis 1918 and operator re-derivation `pg:wick`. -/
def GaussianPairings : ℕ → Type
  | 0 => Unit
  | 1 => Empty
  | m + 2 => Fin (m + 1) × GaussianPairings m

/-- The canonical complete pairing family is finite. Source: operator
re-derivation `pg:wick`; the construction includes odd and empty lengths. -/
@[instance_reducible] def gaussianPairingsFintype : (m : ℕ) → Fintype (GaussianPairings m)
  | 0 => inferInstanceAs (Fintype Unit)
  | 1 => inferInstanceAs (Fintype Empty)
  | m + 2 => by
      letI := gaussianPairingsFintype m
      exact inferInstanceAs (Fintype (Fin (m + 1) × GaussianPairings m))

attribute [instance] gaussianPairingsFintype

/-- The product of covariance entries over the unordered pairs of a canonical
complete pairing. Source: operator re-derivation `pg:wick`. -/
def gaussianPairingWeight : {m : ℕ} →
    (Fin m → Fin m → ℝ) → GaussianPairings m → ℝ
  | 0, _, _ => 1
  | 1, _, π => Empty.elim π
  | _m + 2, C, (j, π) => C 0 j.succ * gaussianPairingWeight
      (fun a b => C (j.succAbove a).succ (j.succAbove b).succ) π

/-- The positions covered by a pairing, listed pair by pair. Source:
operator re-derivation `pg:wick`; this records its literal combinatorial scope. -/
def gaussianPairingPositions : {m : ℕ} → GaussianPairings m → List (Fin m)
  | 0, _ => []
  | 1, π => Empty.elim π
  | _m + 2, (j, π) => 0 :: j.succ ::
      (gaussianPairingPositions π).map (fun a => (j.succAbove a).succ)

/-- A complete pairing covers exactly its number of labelled positions.
Source: the finite pairing construction in operator re-derivation `pg:wick`. -/
theorem gaussianPairingPositions_length {m : ℕ} (π : GaussianPairings m) :
    (gaussianPairingPositions π).length = m := by
  induction m using Nat.twoStepInduction with
  | zero => rfl
  | one => exact Empty.elim π
  | more m ih _ =>
      rcases π with ⟨j, π⟩
      simp only [gaussianPairingPositions, List.length_cons, List.length_map, ih]

/-- Every position appears in a canonical complete pairing. Together with the
exact length, this says each position appears once.
Source: operator re-derivation `pg:wick`. -/
theorem gaussianPairingPositions_toFinset {m : ℕ} (π : GaussianPairings m) :
    (gaussianPairingPositions π).toFinset = Finset.univ := by
  induction m using Nat.twoStepInduction with
  | zero => simp [gaussianPairingPositions]
  | one => exact Empty.elim π
  | more m ih _ =>
      rcases π with ⟨j, π⟩
      simp only [gaussianPairingPositions, List.toFinset_cons]
      have htail : ∀ a : Fin m, a ∈ gaussianPairingPositions π := by
        intro a
        apply List.mem_toFinset.mp
        rw [ih]
        exact Finset.mem_univ a
      ext i
      constructor
      · intro _; exact Finset.mem_univ _
      · intro _
        refine Fin.cases ?_ (fun b => ?_) i
        · simp
        · rcases Fin.eq_self_or_eq_succAbove j b with rfl | ⟨a, rfl⟩
          · simp
          · simp only [Finset.mem_insert, List.mem_toFinset, List.mem_map]
            exact Or.inr (Or.inr ⟨a, htail a, rfl⟩)

/-- A complete pairing uses every labelled position exactly once.
Source: operator re-derivation `pg:wick`; this rules out reused positions. -/
theorem gaussianPairingPositions_nodup {m : ℕ} (π : GaussianPairings m) :
    (gaussianPairingPositions π).Nodup := by
  apply (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (gaussianPairingPositions π : Multiset (Fin m)))).mp
  change (gaussianPairingPositions π).toFinset.card = (gaussianPairingPositions π).length
  rw [gaussianPairingPositions_toFinset, gaussianPairingPositions_length,
    Finset.card_univ, Fintype.card_fin]

/-- Gaussian Wick's finite pairing sum for arbitrary products of linear forms
under independent standard coordinates, including singular images and repeated
coefficient vectors. Source: operator re-derivation `pg:wick`.
atlas: isserlis (partial) -/
theorem integral_prod_dotProduct_eq_sum_gaussianPairingWeight
    {n m : ℕ} (a : Fin m → Fin n → ℝ) :
    ∫ x : Fin n → ℝ, ∏ j, a j ⬝ᵥ x ∂Measure.pi (fun _ => gaussianReal 0 1) =
      ∑ π : GaussianPairings m, gaussianPairingWeight (fun i j => a i ⬝ᵥ a j) π := by
  induction m using Nat.twoStepInduction with
  | zero =>
      have : Unique (GaussianPairings 0) := inferInstanceAs (Unique Unit)
      have hsum : (∑ π : GaussianPairings 0,
          gaussianPairingWeight (fun i j => a i ⬝ᵥ a j) π) = 1 := by
        rw [Fintype.sum_unique]
        rfl
      rw [hsum]
      simp
  | one =>
      have hh := integral_dotProduct_mul_prod_pi_gaussianReal
        (∅ : Finset (Fin 0)) (fun j => Fin.elim0 j) (a 0)
      have : IsEmpty (GaussianPairings 1) := inferInstanceAs (IsEmpty Empty)
      have hsum : (∑ π : GaussianPairings 1,
          gaussianPairingWeight (fun i j => a i ⬝ᵥ a j) π) = 0 := by simp
      rw [hsum]
      simpa using hh
  | more m ih _ =>
      have hrec := integral_dotProduct_mul_prod_pi_gaussianReal
        (Finset.univ : Finset (Fin (m + 1))) (fun j => a j.succ) (a 0)
      have hprod : ∀ x : Fin n → ℝ,
          (∏ j : Fin (m + 2), a j ⬝ᵥ x) =
          (a 0 ⬝ᵥ x) * ∏ j : Fin (m + 1), a j.succ ⬝ᵥ x :=
        fun x => Fin.prod_univ_succ _
      simp_rw [hprod]
      rw [hrec]
      have herase : ∀ j : Fin (m + 1), ∀ x : Fin n → ℝ,
          (∏ k ∈ Finset.univ.erase j, a k.succ ⬝ᵥ x) =
          ∏ k : Fin m, a (j.succAbove k).succ ⬝ᵥ x := by
        intro j x
        rw [Fin.univ_succAbove m j, Finset.erase_cons, Finset.prod_map]
        rfl
      simp_rw [herase, ih]
      change _ = ∑ π : Fin (m + 1) × GaussianPairings m,
        (a 0 ⬝ᵥ a π.1.succ) * gaussianPairingWeight
          (fun i j => a (π.1.succAbove i).succ ⬝ᵥ a (π.1.succAbove j).succ) π.2
      rw [Fintype.sum_prod_type]
      simp only [Finset.mul_sum]

/-- Every odd centered standard-Gaussian linear product has expectation zero,
without distinctness or nonsingularity assumptions. Source: operator
re-derivation `pg:wick`.
atlas: isserlis (partial) -/
theorem integral_prod_dotProduct_eq_zero_of_odd
    {n m : ℕ} (hm : Odd m) (a : Fin m → Fin n → ℝ) :
    ∫ x : Fin n → ℝ, ∏ j, a j ⬝ᵥ x ∂Measure.pi (fun _ => gaussianReal 0 1) = 0 := by
  rw [integral_prod_dotProduct_eq_sum_gaussianPairingWeight]
  have hEmpty : ∀ m : ℕ, Odd m → IsEmpty (GaussianPairings m) := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => intro h; simp at h
    | one => intro _; exact inferInstanceAs (IsEmpty Empty)
    | more m ih _ =>
        intro h
        have hm : Odd m := by
          rcases h with ⟨r, hr⟩
          cases r with
          | zero => omega
          | succ r => exact ⟨r, by omega⟩
        have := ih hm
        exact inferInstanceAs (IsEmpty (Fin (m + 1) × GaussianPairings m))
  have := hEmpty m hm
  simp

end NLAlib
