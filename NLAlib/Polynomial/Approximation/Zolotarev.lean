import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.Compact

/-!
# Zolotarev separation numbers

Admissible polynomial pairs exclude denominator zeros on the left set and
numerator zeros on the right set. The right-hand ratio is `q/p`, so poles
of `p/q` on the right set are included correctly. The infimum is represented
in `ℝ≥0∞`; the constant competitor proves it is at most one and hence finite.
-/

noncomputable section
open Polynomial
open scoped ENNReal NNReal
namespace NLAlib

/-- A degree-bounded rational competitor, with the pole convention required
for displacement singular-value bounds. -/
structure ZolotarevPair (E F : Set ℂ) (k : ℕ) where
  numerator : ℂ[X]
  denominator : ℂ[X]
  numerator_degree : numerator.natDegree ≤ k
  denominator_degree : denominator.natDegree ≤ k
  denominator_ne_zero : ∀ z ∈ E, denominator.eval (z : ℂ) ≠ 0
  numerator_ne_zero : ∀ z ∈ F, numerator.eval (z : ℂ) ≠ 0

namespace ZolotarevPair
variable {E F E' F' : Set ℂ} {k l : ℕ}

/-- The actual product of the two suprema, with a reciprocal on the right. -/
def cost (P : ZolotarevPair E F k) : ℝ≥0∞ :=
  (⨆ z : E, (‖P.numerator.eval (z : ℂ) / P.denominator.eval (z : ℂ)‖₊ : ℝ≥0∞)) *
    (⨆ z : F, (‖P.denominator.eval (z : ℂ) / P.numerator.eval (z : ℂ)‖₊ : ℝ≥0∞))

/-- The supremum of the rational modulus on the left set. -/
def leftSup (P : ZolotarevPair E F k) : ℝ≥0∞ :=
  ⨆ z : E, (‖P.numerator.eval (z : ℂ) / P.denominator.eval (z : ℂ)‖₊ : ℝ≥0∞)

/-- The supremum of the reciprocal modulus on the right set. -/
def rightSup (P : ZolotarevPair E F k) : ℝ≥0∞ :=
  ⨆ z : F, (‖P.denominator.eval (z : ℂ) / P.numerator.eval (z : ℂ)‖₊ : ℝ≥0∞)

/-- The constant rational competitor. -/
def one (E F : Set ℂ) (k : ℕ) : ZolotarevPair E F k where
  numerator := 1
  denominator := 1
  numerator_degree := by simp
  denominator_degree := by simp
  denominator_ne_zero := by simp
  numerator_ne_zero := by simp

instance (E F : Set ℂ) (k : ℕ) : Nonempty (ZolotarevPair E F k) := ⟨one E F k⟩

/-- The constant competitor never costs more than one, including empty sets. -/
theorem cost_one_le (E F : Set ℂ) (k : ℕ) : (one E F k).cost ≤ 1 := by
  unfold cost
  have h₁ : (⨆ z : E, (‖(one E F k).numerator.eval (z : ℂ) /
      (one E F k).denominator.eval (z : ℂ)‖₊ : ℝ≥0∞)) ≤ 1 := by simp [one]
  have h₂ : (⨆ z : F, (‖(one E F k).denominator.eval (z : ℂ) /
      (one E F k).numerator.eval (z : ℂ)‖₊ : ℝ≥0∞)) ≤ 1 := by simp [one]
  simpa using mul_le_mul' h₁ h₂

/-- Degree enlargement leaves the underlying rational function unchanged. -/
def enlarge (P : ZolotarevPair E F k) (h : k ≤ l) : ZolotarevPair E F l :=
  { P with numerator_degree := P.numerator_degree.trans h
           denominator_degree := P.denominator_degree.trans h }

/-- Restriction of the two compact sets retains admissibility. -/
def restrict (P : ZolotarevPair E F k) (hE : E' ⊆ E) (hF : F' ⊆ F) :
    ZolotarevPair E' F' k :=
  { P with denominator_ne_zero := fun z hz => P.denominator_ne_zero z (hE hz)
           numerator_ne_zero := fun z hz => P.numerator_ne_zero z (hF hz) }

/-- Reciprocal rational functions exchange the two sets. -/
def swap (P : ZolotarevPair E F k) : ZolotarevPair F E k where
  numerator := P.denominator
  denominator := P.numerator
  numerator_degree := P.denominator_degree
  denominator_degree := P.numerator_degree
  denominator_ne_zero := P.numerator_ne_zero
  numerator_ne_zero := P.denominator_ne_zero

/-- Multiplying two actual rational competitors adds their degree budgets. -/
def mul (P : ZolotarevPair E F k) (Q : ZolotarevPair E F l) : ZolotarevPair E F (k + l) where
  numerator := P.numerator * Q.numerator
  denominator := P.denominator * Q.denominator
  numerator_degree := natDegree_mul_le.trans (Nat.add_le_add P.numerator_degree Q.numerator_degree)
  denominator_degree := natDegree_mul_le.trans (Nat.add_le_add P.denominator_degree Q.denominator_degree)
  denominator_ne_zero := fun z hz => by
    simpa using mul_ne_zero (P.denominator_ne_zero z hz) (Q.denominator_ne_zero z hz)
  numerator_ne_zero := fun z hz => by
    simpa using mul_ne_zero (P.numerator_ne_zero z hz) (Q.numerator_ne_zero z hz)

/-- Restricting sets cannot increase a competitor's separation cost. -/
theorem cost_restrict_le (P : ZolotarevPair E F k) (hE : E' ⊆ E) (hF : F' ⊆ F) :
    (P.restrict hE hF).cost ≤ P.cost := by
  unfold cost
  apply mul_le_mul'
  · apply iSup_le; intro z
    exact le_iSup_of_le (⟨z, hE z.property⟩ : E) le_rfl
  · apply iSup_le; intro z
    exact le_iSup_of_le (⟨z, hF z.property⟩ : F) le_rfl

/-- The cost of a product is at most the product of the costs. -/
theorem cost_mul_le (P : ZolotarevPair E F k) (Q : ZolotarevPair E F l) :
    (P.mul Q).cost ≤ P.cost * Q.cost := by
  let a := ⨆ z : E, (‖P.numerator.eval (z : ℂ) / P.denominator.eval (z : ℂ)‖₊ : ℝ≥0∞)
  let b := ⨆ z : F, (‖P.denominator.eval (z : ℂ) / P.numerator.eval (z : ℂ)‖₊ : ℝ≥0∞)
  let c := ⨆ z : E, (‖Q.numerator.eval (z : ℂ) / Q.denominator.eval (z : ℂ)‖₊ : ℝ≥0∞)
  let d := ⨆ z : F, (‖Q.denominator.eval (z : ℂ) / Q.numerator.eval (z : ℂ)‖₊ : ℝ≥0∞)
  have hleft : (⨆ z : E, (‖(P.numerator * Q.numerator).eval (z : ℂ) /
      (P.denominator * Q.denominator).eval (z : ℂ)‖₊ : ℝ≥0∞)) ≤ a * c := by
    dsimp only [a, c]
    apply iSup_le; intro z
    simp only [eval_mul, ← div_mul_div_comm, nnnorm_mul, ENNReal.coe_mul]
    exact mul_le_mul'
      (le_iSup (fun w : E => (‖P.numerator.eval (w : ℂ) / P.denominator.eval (w : ℂ)‖₊ : ℝ≥0∞)) z)
      (le_iSup (fun w : E => (‖Q.numerator.eval (w : ℂ) / Q.denominator.eval (w : ℂ)‖₊ : ℝ≥0∞)) z)
  have hright : (⨆ z : F, (‖(P.denominator * Q.denominator).eval (z : ℂ) /
      (P.numerator * Q.numerator).eval (z : ℂ)‖₊ : ℝ≥0∞)) ≤ b * d := by
    dsimp only [b, d]
    apply iSup_le; intro z
    simp only [eval_mul, ← div_mul_div_comm, nnnorm_mul, ENNReal.coe_mul]
    exact mul_le_mul'
      (le_iSup (fun w : F => (‖P.denominator.eval (w : ℂ) / P.numerator.eval (w : ℂ)‖₊ : ℝ≥0∞)) z)
      (le_iSup (fun w : F => (‖Q.denominator.eval (w : ℂ) / Q.numerator.eval (w : ℂ)‖₊ : ℝ≥0∞)) z)
  exact (mul_le_mul' hleft hright).trans_eq (by dsimp [cost, mul, a, b, c, d]; ac_rfl)

/-- Compactness and the nonvanishing conditions make each scalar supremum
finite, and consequently make every admissible cost finite. -/
theorem cost_ne_top (P : ZolotarevPair E F k) (hE : IsCompact E) (hF : IsCompact F) :
    P.cost ≠ ⊤ := by
  have hleft : (⨆ z : E, (‖P.numerator.eval (z : ℂ) /
      P.denominator.eval (z : ℂ)‖₊ : ℝ≥0∞)) < ⊤ := by
    apply ENNReal.iSup_coe_lt_top.mpr
    obtain ⟨c, hc⟩ := hE.bddAbove_image
      ((P.numerator.continuous.continuousOn.div P.denominator.continuous.continuousOn
        P.denominator_ne_zero).nnnorm)
    refine ⟨c, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hc ⟨z, z.property, rfl⟩
  have hright : (⨆ z : F, (‖P.denominator.eval (z : ℂ) /
      P.numerator.eval (z : ℂ)‖₊ : ℝ≥0∞)) < ⊤ := by
    apply ENNReal.iSup_coe_lt_top.mpr
    obtain ⟨c, hc⟩ := hF.bddAbove_image
      ((P.denominator.continuous.continuousOn.div P.numerator.continuous.continuousOn
        P.numerator_ne_zero).nnnorm)
    refine ⟨c, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hc ⟨z, z.property, rfl⟩
  exact ENNReal.mul_ne_top hleft.ne hright.ne

/-- The left supremum is finite on a compact set. -/
theorem leftSup_ne_top (P : ZolotarevPair E F k) (hE : IsCompact E) : P.leftSup ≠ ⊤ := by
  apply ne_of_lt
  apply ENNReal.iSup_coe_lt_top.mpr
  obtain ⟨c, hc⟩ := hE.bddAbove_image
    ((P.numerator.continuous.continuousOn.div P.denominator.continuous.continuousOn
      P.denominator_ne_zero).nnnorm)
  refine ⟨c, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hc ⟨z, z.property, rfl⟩

/-- The reciprocal supremum is finite on a compact set. -/
theorem rightSup_ne_top (P : ZolotarevPair E F k) (hF : IsCompact F) : P.rightSup ≠ ⊤ :=
  P.swap.leftSup_ne_top hF

/-- The finite supremum bounds the scalar rational modulus. -/
theorem norm_div_le_leftSup_toReal (P : ZolotarevPair E F k) (hE : IsCompact E)
    {z : ℂ} (hz : z ∈ E) : ‖P.numerator.eval z / P.denominator.eval z‖ ≤ P.leftSup.toReal := by
  have h := ENNReal.toReal_mono (P.leftSup_ne_top hE)
    (le_iSup (fun w : E => (‖P.numerator.eval (w : ℂ) / P.denominator.eval (w : ℂ)‖₊ : ℝ≥0∞)) ⟨z, hz⟩)
  simpa using h

/-- The right supremum bounds the scalar reciprocal modulus. -/
theorem norm_div_le_rightSup_toReal (P : ZolotarevPair E F k) (hF : IsCompact F)
    {z : ℂ} (hz : z ∈ F) : ‖P.denominator.eval z / P.numerator.eval z‖ ≤ P.rightSup.toReal :=
  P.swap.norm_div_le_leftSup_toReal hF hz

/-- Every admissible degree-zero competitor has cost one on nonempty sets. -/
theorem cost_degree_zero (P : ZolotarevPair E F 0) (hE : E.Nonempty) (hF : F.Nonempty) :
    P.cost = 1 := by
  let : Nonempty E := hE.to_subtype
  let : Nonempty F := hF.to_subtype
  obtain ⟨a, hp⟩ : ∃ a : ℂ, P.numerator = C a :=
    ⟨_, eq_C_of_natDegree_le_zero P.numerator_degree⟩
  obtain ⟨b, hq⟩ : ∃ b : ℂ, P.denominator = C b :=
    ⟨_, eq_C_of_natDegree_le_zero P.denominator_degree⟩
  have hpn : a ≠ 0 := by
    obtain ⟨z, hz⟩ := hF
    simpa only [hp, eval_C] using P.numerator_ne_zero z hz
  have hqn : b ≠ 0 := by
    obtain ⟨z, hz⟩ := hE
    simpa only [hq, eval_C] using P.denominator_ne_zero z hz
  unfold cost
  simp only [hp, hq, eval_C, iSup_const, ← ENNReal.coe_mul]
  have hnorm : ‖a / b‖₊ * ‖b / a‖₊ = 1 := by
    have hab : a / b * (b / a) = 1 := by field_simp
    rw [← nnnorm_mul, hab, nnnorm_one]
  rw [hnorm, ENNReal.coe_one]

end ZolotarevPair

/-- The Zolotarev number is the infimum over actual admissible polynomial
pairs, never over hypothesized approximation errors. The extended nonnegative
representation has no infinity value, by `zolotarevNumber_le_one`. -/
def zolotarevNumber (E F : Set ℂ) (k : ℕ) : ℝ≥0∞ := ⨅ P : ZolotarevPair E F k, P.cost

/-- A Zolotarev number is nonnegative. -/
theorem zolotarevNumber_nonneg (E F : Set ℂ) (k : ℕ) : 0 ≤ zolotarevNumber E F k := bot_le

/-- Constant competitors bound every Zolotarev number by one. -/
theorem zolotarevNumber_le_one (E F : Set ℂ) (k : ℕ) : zolotarevNumber E F k ≤ 1 :=
  (iInf_le _ (ZolotarevPair.one E F k)).trans (ZolotarevPair.cost_one_le E F k)

/-- The infimum represents a finite real number. -/
theorem zolotarevNumber_ne_top (E F : Set ℂ) (k : ℕ) : zolotarevNumber E F k ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (zolotarevNumber_le_one E F k)

/-- Nonempty sets have degree-zero Zolotarev number exactly one.
Together with the pole-aware admissible-pair definition, monotonicity,
symmetry and submultiplicativity this realizes the defining Zolotarev API.
Source: user derivations, Zolotarev-number definition.
atlas: zolotarev-number-def -/
theorem zolotarevNumber_zero (E F : Set ℂ) (hE : E.Nonempty) (hF : F.Nonempty) :
    zolotarevNumber E F 0 = 1 := by
  apply le_antisymm (zolotarevNumber_le_one E F 0)
  apply le_iInf
  intro P
  exact (P.cost_degree_zero hE hF).ge

/-- Enlarging the degree budget improves the best separation. -/
theorem zolotarevNumber_antitone (E F : Set ℂ) : Antitone (zolotarevNumber E F) := by
  intro k l h
  apply le_iInf; intro P
  exact iInf_le_of_le (P.enlarge h) le_rfl

/-- Enlarging either set can only increase the Zolotarev number. -/
theorem zolotarevNumber_mono_sets {E F E' F' : Set ℂ} (hE : E' ⊆ E) (hF : F' ⊆ F) (k : ℕ) :
    zolotarevNumber E' F' k ≤ zolotarevNumber E F k := by
  apply le_iInf; intro P
  exact (iInf_le _ (P.restrict hE hF)).trans (P.cost_restrict_le hE hF)

/-- Exchanging the two sets reciprocates every admissible rational function. -/
theorem zolotarevNumber_symm (E F : Set ℂ) (k : ℕ) :
    zolotarevNumber E F k = zolotarevNumber F E k := by
  have h (E F : Set ℂ) : zolotarevNumber E F k ≤ zolotarevNumber F E k := by
    apply le_iInf; intro P
    exact iInf_le_of_le P.swap (by dsimp [ZolotarevPair.cost, ZolotarevPair.swap]; rw [mul_comm])
  exact le_antisymm (h E F) (h F E)

/-- Submultiplicativity follows from actual products of admissible competitors;
no minimizing pair is assumed to exist. Source: user derivations, Zolotarev numbers.
atlas: zolotarev-number-def (partial) -/
theorem zolotarevNumber_add_le (E F : Set ℂ) (k l : ℕ) :
    zolotarevNumber E F (k + l) ≤ zolotarevNumber E F k * zolotarevNumber E F l := by
  apply ENNReal.le_iInf_mul_iInf
    ⟨ZolotarevPair.one E F k, ne_top_of_le_ne_top (by simp) (ZolotarevPair.cost_one_le E F k)⟩
    ⟨ZolotarevPair.one E F l, ne_top_of_le_ne_top (by simp) (ZolotarevPair.cost_one_le E F l)⟩
  intro P Q
  exact (iInf_le _ (P.mul Q)).trans (P.cost_mul_le Q)

end NLAlib
