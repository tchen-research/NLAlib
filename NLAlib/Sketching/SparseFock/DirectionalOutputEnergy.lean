/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.DirectionalOccupationEnergy

set_option autoImplicit false

/-!
# Directional output synthesis energy

Coefficient-energy identities and marked synthesis bounds for all directional output fibers.
Ported from `SparseFockFormal.DirectionalConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace DirectionalConcrete

open ParsevalFrame LocalOperator BandInventory FiniteOperator ExternalOperator
  GlobalBands NamedBands FiniteHilbert
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- The row-local coefficient squares after `Y₊` synthesis are exactly the
finite marked-output sum.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_output_coeff_energy_eq (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ∑ a ∈ p.heavyInRow r,
        (contract F c x
          (setPair p (r, a) .one (r, c) .zero)) ^ 2) =
      ∑ z : RowMark m n .two .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .one
            (z.row, z.right) .zero)) ^ 2 := by
  rw [sum_rowMark_eq_nested (m := m) (n := n) .two .one
    (fun p r a c ↦ (contract F c x
      (setPair p (r, a) .one (r, c) .zero)) ^ 2)]
  simp only [levelInRow_two, levelInRow_one]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hnot : a ∉ p.lightInRow r := by
    intro hlight
    have haTwo : p (r, a) = .two := by simpa using ha
    have haOne : p (r, a) = .one := by simpa using hlight
    simp_all
  rw [Finset.erase_eq_self.mpr hnot]

/-- The corresponding exact marked-output identity for `Y₀`.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_output_coeff_energy_eq (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ∑ a ∈ (p.lightInRow r).erase c,
        (contract F c x
          (setPair p (r, a) .two (r, c) .zero)) ^ 2) =
      ∑ z : RowMark m n .one .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .two
            (z.row, z.right) .zero)) ^ 2 := by
  rw [sum_rowMark_eq_nested (m := m) (n := n) .one .one
    (fun p r a c ↦ (contract F c x
      (setPair p (r, a) .two (r, c) .zero)) ^ 2)]
  simp only [levelInRow_one]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  exact sum_erase_comm (p.lightInRow r)
    (fun a c ↦ (contract F c x
      (setPair p (r, a) .two (r, c) .zero)) ^ 2) |>.symm

/-- The corresponding exact marked-output identity for the transpose hop.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_output_coeff_energy_eq (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ∑ a ∈ p.freshInRow r,
        (contract F c x
          (setPair p (r, a) .one (r, c) .zero)) ^ 2) =
      ∑ z : RowMark m n .zero .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .one
            (z.row, z.right) .zero)) ^ 2 := by
  rw [sum_rowMark_eq_nested (m := m) (n := n) .zero .one
    (fun p r a c ↦ (contract F c x
      (setPair p (r, a) .one (r, c) .zero)) ^ 2)]
  simp only [levelInRow_zero, levelInRow_one]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hnot : a ∉ p.lightInRow r := by
    intro hlight
    have haZero : p (r, a) = .zero := by simpa using ha
    have haOne : p (r, a) = .one := by simpa using hlight
    simp_all
  rw [Finset.erase_eq_self.mpr hnot]

/-- Mixed raising synthesis energy is bounded by the finite marked-pair contraction energy.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_marked_synthesis_energy_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ParsevalFrame.normSq (yPlusMarked F x p r c)) ≤
      markedEnergy .one .zero F x := by
  calc
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yPlusMarked F x p r c)) ≤
        ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ∑ a ∈ p.heavyInRow r,
            (contract F c x
              (setPair p (r, a) .one (r, c) .zero)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro c _
      exact yPlusMarked_normSq_le F x p r c
    _ = ∑ z : RowMark m n .two .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .one
            (z.row, z.right) .zero)) ^ 2 := Yplus_output_coeff_energy_eq F x
    _ = markedEnergy .one .zero F x := Yplus_marked_reindex F x

/-- Mixed preserving synthesis energy is bounded by the finite marked-pair contraction energy.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_marked_synthesis_energy_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ParsevalFrame.normSq (yZeroMarked F x p r c)) ≤
      markedEnergy .two .zero F x := by
  calc
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yZeroMarked F x p r c)) ≤
        ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ∑ a ∈ (p.lightInRow r).erase c,
            (contract F c x
              (setPair p (r, a) .two (r, c) .zero)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro c _
      exact yZeroMarked_normSq_le F x p r c
    _ = ∑ z : RowMark m n .one .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .two
            (z.row, z.right) .zero)) ^ 2 := Yzero_output_coeff_energy_eq F x
    _ = markedEnergy .two .zero F x := Yzero_marked_reindex F x

/-- Heavy correction synthesis energy is bounded by the finite marked-pair contraction energy.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_marked_synthesis_energy_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
      ParsevalFrame.normSq (hprimeMarked F x p r c)) ≤
      markedEnergy .one .zero F x := by
  calc
    (∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (hprimeMarked F x p r c)) ≤
        ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ∑ a ∈ p.freshInRow r,
            (contract F c x
              (setPair p (r, a) .one (r, c) .zero)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro c _
      exact hprimeMarked_normSq_le F x p r c
    _ = ∑ z : RowMark m n .zero .one,
        (contract F z.right x
          (setPair z.pattern (z.row, z.left) .one
            (z.row, z.right) .zero)) ^ 2 := Hprime_output_coeff_energy_eq F x
    _ = markedEnergy .one .zero F x := Hprime_marked_reindex F x

/-- A mixed raising output fiber has energy bounded by its admissible marked contributions.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_output_fiber_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    (p : Pattern m n) :
    ParsevalFrame.normSq
      (fullFiber (Matrix.mulVec (Yplus m (frameRows F)) x) p) ≤
      (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yPlusMarked F x p r c) := by
  by_cases hp : p.grade = nu + 2
  · by_cases hheavy : p.heavy.Nonempty
    · have hcardNat : p.light.card ≤ nu := by
        have hformula := p.grade_eq_card_light_add_two_mul_card_heavy
        have hone : 1 ≤ p.heavy.card := Finset.one_le_card.mpr hheavy
        omega
      have hcard : (p.light.card : ℝ) ≤ (nu : ℝ) := by
        exact_mod_cast hcardNat
      rw [Yplus_fullFiber]
      calc
        ParsevalFrame.normSq
            (∑ s ∈ p.light, yPlusMarked F x p s.1 s.2) ≤
            (p.light.card : ℝ) * ∑ s ∈ p.light,
              ParsevalFrame.normSq (yPlusMarked F x p s.1 s.2) :=
          normSq_sum_le_card p.light
            (fun s ↦ yPlusMarked F x p s.1 s.2)
        _ = (p.light.card : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
              ParsevalFrame.normSq (yPlusMarked F x p r c) := by
          rw [← sum_rows_light_eq_sum_light p
            (fun s ↦ ParsevalFrame.normSq (yPlusMarked F x p s.1 s.2))]
        _ ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
              ParsevalFrame.normSq (yPlusMarked F x p r c) := by
          apply mul_le_mul_of_nonneg_right hcard
          exact Finset.sum_nonneg fun r _ ↦
            Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg
    · have hempty : p.heavy = ∅ := Finset.not_nonempty_iff_eq_empty.mp hheavy
      have hrow (r : Fin m) : p.heavyInRow r = ∅ := by
        ext a
        constructor
        · intro ha
          have hsite : (r, a) ∈ p.heavy := by simpa using ha
          simp [hempty] at hsite
        · simp
      have hzero (r : Fin m) (c : Fin n) :
          ParsevalFrame.normSq (yPlusMarked F x p r c) = 0 := by
        have hle := yPlusMarked_normSq_le F x p r c
        rw [hrow] at hle
        simp only [Finset.sum_empty] at hle
        exact le_antisymm hle real_inner_self_nonneg
      rw [Yplus_fullFiber]
      calc
        ParsevalFrame.normSq
            (∑ s ∈ p.light, yPlusMarked F x p s.1 s.2) ≤
            (p.light.card : ℝ) * ∑ s ∈ p.light,
              ParsevalFrame.normSq (yPlusMarked F x p s.1 s.2) :=
          normSq_sum_le_card p.light
            (fun s ↦ yPlusMarked F x p s.1 s.2)
        _ = 0 := by simp [hzero]
        _ ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
              ParsevalFrame.normSq (yPlusMarked F x p r c) := by
          exact mul_nonneg (Nat.cast_nonneg nu)
            (Finset.sum_nonneg fun r _ ↦
              Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg)
  · have hpInt : (p.grade : ℤ) ≠ (nu : ℤ) + 2 := by
      intro h
      apply hp
      exact_mod_cast h
    have hz := fullFiber_mulVec_eq_zero_of_grade
      (Yplus_homogeneous (m := m) F) hx p hpInt
    rw [hz]
    have hrhs : 0 ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yPlusMarked F x p r c) :=
      mul_nonneg (Nat.cast_nonneg nu)
        (Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg)
    simpa [ParsevalFrame.normSq] using hrhs

/-- A mixed preserving output fiber has energy bounded by its admissible marked contributions.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_output_fiber_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    (p : Pattern m n) :
    ParsevalFrame.normSq
      (fullFiber (Matrix.mulVec (Yzero m (frameRows F)) x) p) ≤
      (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yZeroMarked F x p r c) := by
  by_cases hp : p.grade = nu
  · have hcardNat : p.light.card ≤ nu := by
      simpa [hp] using p.card_light_le_grade
    have hcard : (p.light.card : ℝ) ≤ (nu : ℝ) := by
      exact_mod_cast hcardNat
    rw [Yzero_fullFiber]
    calc
      ParsevalFrame.normSq
          (∑ s ∈ p.light, yZeroMarked F x p s.1 s.2) ≤
          (p.light.card : ℝ) * ∑ s ∈ p.light,
            ParsevalFrame.normSq (yZeroMarked F x p s.1 s.2) :=
        normSq_sum_le_card p.light
          (fun s ↦ yZeroMarked F x p s.1 s.2)
      _ = (p.light.card : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
            ParsevalFrame.normSq (yZeroMarked F x p r c) := by
        rw [← sum_rows_light_eq_sum_light p
          (fun s ↦ ParsevalFrame.normSq (yZeroMarked F x p s.1 s.2))]
      _ ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
            ParsevalFrame.normSq (yZeroMarked F x p r c) := by
        apply mul_le_mul_of_nonneg_right hcard
        exact Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg
  · have hpInt : (p.grade : ℤ) ≠ (nu : ℤ) + 0 := by
      intro h
      apply hp
      have h' : (p.grade : ℤ) = (nu : ℤ) := by simpa using h
      exact_mod_cast h'
    have hz := fullFiber_mulVec_eq_zero_of_grade
      (Yzero_homogeneous (m := m) F) hx p hpInt
    rw [hz]
    have hrhs : 0 ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (yZeroMarked F x p r c) :=
      mul_nonneg (Nat.cast_nonneg nu)
        (Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg)
    simpa [ParsevalFrame.normSq] using hrhs

/-- A heavy correction output fiber has energy bounded by its admissible marked contributions.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_output_fiber_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x)
    (p : Pattern m n) :
    ParsevalFrame.normSq
      (fullFiber (Matrix.mulVec (Hprime m (frameRows F)) x) p) ≤
      (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (hprimeMarked F x p r c) := by
  by_cases hp : p.grade = nu
  · have hcardNat : p.light.card ≤ nu := by
      simpa [hp] using p.card_light_le_grade
    have hcard : (p.light.card : ℝ) ≤ (nu : ℝ) := by
      exact_mod_cast hcardNat
    rw [Hprime_fullFiber]
    calc
      ParsevalFrame.normSq
          (∑ s ∈ p.light, hprimeMarked F x p s.1 s.2) ≤
          (p.light.card : ℝ) * ∑ s ∈ p.light,
            ParsevalFrame.normSq (hprimeMarked F x p s.1 s.2) :=
        normSq_sum_le_card p.light
          (fun s ↦ hprimeMarked F x p s.1 s.2)
      _ = (p.light.card : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
            ParsevalFrame.normSq (hprimeMarked F x p r c) := by
        rw [← sum_rows_light_eq_sum_light p
          (fun s ↦ ParsevalFrame.normSq (hprimeMarked F x p s.1 s.2))]
      _ ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
            ParsevalFrame.normSq (hprimeMarked F x p r c) := by
        apply mul_le_mul_of_nonneg_right hcard
        exact Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg
  · have hpInt : (p.grade : ℤ) ≠ (nu : ℤ) + 0 := by
      intro h
      apply hp
      have h' : (p.grade : ℤ) = (nu : ℤ) := by simpa using h
      exact_mod_cast h'
    have hz := fullFiber_mulVec_eq_zero_of_grade
      (Hprime_homogeneous (m := m) F) hx p hpInt
    rw [hz]
    have hrhs : 0 ≤ (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
        ParsevalFrame.normSq (hprimeMarked F x p r c) :=
      mul_nonneg (Nat.cast_nonneg nu)
        (Finset.sum_nonneg fun r _ ↦
          Finset.sum_nonneg fun c _ ↦ real_inner_self_nonneg)
    simpa [ParsevalFrame.normSq] using hrhs

/-- The total mixed raising output energy is bounded by its marked-pair energy.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_output_energy_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Yplus m (frameRows F)) x) ≤
      (nu : ℝ) * markedEnergy .one .zero F x := by
  rw [full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (Yplus m (frameRows F)) x) p)) ≤
        ∑ p, (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (yPlusMarked F x p r c) := by
      exact Finset.sum_le_sum fun p _ ↦ Yplus_output_fiber_le_marked F hx p
    _ = (nu : ℝ) * ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (yPlusMarked F x p r c) := by
      rw [Finset.mul_sum]
    _ ≤ (nu : ℝ) * markedEnergy .one .zero F x := by
      exact mul_le_mul_of_nonneg_left
        (Yplus_marked_synthesis_energy_le F x) (Nat.cast_nonneg nu)

/-- The total mixed preserving output energy is bounded by its marked-pair energy.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_output_energy_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Yzero m (frameRows F)) x) ≤
      (nu : ℝ) * markedEnergy .two .zero F x := by
  rw [full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (Yzero m (frameRows F)) x) p)) ≤
        ∑ p, (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (yZeroMarked F x p r c) := by
      exact Finset.sum_le_sum fun p _ ↦ Yzero_output_fiber_le_marked F hx p
    _ = (nu : ℝ) * ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (yZeroMarked F x p r c) := by
      rw [Finset.mul_sum]
    _ ≤ (nu : ℝ) * markedEnergy .two .zero F x := by
      exact mul_le_mul_of_nonneg_left
        (Yzero_marked_synthesis_energy_le F x) (Nat.cast_nonneg nu)

/-- The total heavy correction output energy is bounded by its marked-pair energy.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_output_energy_le_marked (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Hprime m (frameRows F)) x) ≤
      (nu : ℝ) * markedEnergy .one .zero F x := by
  rw [full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (Hprime m (frameRows F)) x) p)) ≤
        ∑ p, (nu : ℝ) * ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (hprimeMarked F x p r c) := by
      exact Finset.sum_le_sum fun p _ ↦ Hprime_output_fiber_le_marked F hx p
    _ = (nu : ℝ) * ∑ p, ∑ r, ∑ c ∈ p.lightInRow r,
          ParsevalFrame.normSq (hprimeMarked F x p r c) := by
      rw [Finset.mul_sum]
    _ ≤ (nu : ℝ) * markedEnergy .one .zero F x := by
      exact mul_le_mul_of_nonneg_left
        (Hprime_marked_synthesis_energy_le F x) (Nat.cast_nonneg nu)

end

end DirectionalConcrete

end NLAlib.SparseFock
