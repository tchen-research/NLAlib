import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import NLAlib.Krylov.Polynomial

/-!
# The grade of a vector and the dimension of Krylov spaces

The *grade* of `b` with respect to `A` is `ν = dim span {Aⁱ b : i ∈ ℕ}`, the degree of the
monic polynomial of least degree annihilating `b` through `A`. It is the single breakdown
vocabulary of the Krylov layer (`docs/KRYLOV_DEFINITIONS.md` §3.1, §6.7):

* `krylovGrade A b`: the grade, defined as a `finrank`;
* `finrank_krylovSpace`: `dim K_q(A,b) = min q ν`;
* `linearIndependent_pow_mulVec_iff_le_krylovGrade`: `b, Ab, …, A^(q−1) b` are linearly
  independent iff `q ≤ ν`;
* `krylovSpace_eq_of_krylovGrade_le`: `K_q = K_ν` for `q ≥ ν`;
* `mulVec_mem_krylovSpace_krylovGrade`: `A K_ν ⊆ K_ν`;
* `krylovGrade_le_natDegree_minpoly`, `krylovGrade_le_card`: `ν ≤ deg μ_A ≤ n`;
* `krylovGrade_eq_zero_iff`: `ν = 0 ↔ b = 0`;
* `sub_mem_krylovSpace_krylovGrade`: finite termination, `x⋆ − x₀ ∈ K_ν(A, r₀)` for invertible
  `A`.

Statements about spaces carry no breakdown hypothesis; statements that need an orthonormal
basis of `K_q` take `q ≤ krylovGrade A b`.

Source: Saad (2003) [`saad03`], Props 6.1–6.3; Liesen–Strakoš (2013) [`ls13`], §2.2.
Atlas: `krylov-grade`.
-/

noncomputable section

open scoped Matrix Polynomial
open Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The grade of `b` with respect to `A`: `ν(A, b) = dim span {Aⁱ b : i ∈ ℕ}`, equivalently the
degree of the monic polynomial `μ_{A,b}` of least degree with `μ_{A,b}(A) b = 0`.
Source: Saad (2003) [`saad03`], Def. before Prop 6.1; Liesen–Strakoš (2013) [`ls13`], §2.2.
Deviation: real scalars only (the atlas entry allows any field).
atlas: krylov-grade (partial) -/
def krylovGrade (A : Matrix n n ℝ) (b : n → ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : ℕ => (A ^ i) *ᵥ b))

variable (A : Matrix n n ℝ) (b : n → ℝ)

/-- Every Krylov space lies in the span of all the `Aⁱ b`. -/
private lemma krylovSpace_le_span_range (q : ℕ) :
    krylovSpace A b q ≤ Submodule.span ℝ (Set.range fun i : ℕ => (A ^ i) *ᵥ b) :=
  Submodule.span_mono <| by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩

/-- Linear independence of `b, …, A^q b` splits off the last vector. -/
private lemma linearIndependent_pow_mulVec_succ_iff (q : ℕ) :
    LinearIndependent ℝ (fun i : Fin (q + 1) => (A ^ (i : ℕ)) *ᵥ b) ↔
      LinearIndependent ℝ (fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b) ∧
        (A ^ q) *ᵥ b ∉ krylovSpace A b q := by
  have h : (fun i : Fin (q + 1) => (A ^ (i : ℕ)) *ᵥ b) =
      Fin.snoc (fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b) ((A ^ q) *ᵥ b) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [h, linearIndependent_finSnoc]
  rfl

/-- If no `Aⁱ b` with `i < q` lies in the previous Krylov space, the first `q` are independent. -/
private lemma linearIndependent_pow_mulVec_of_forall_not_mem {q : ℕ}
    (h : ∀ i < q, (A ^ i) *ᵥ b ∉ krylovSpace A b i) :
    LinearIndependent ℝ (fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b) := by
  induction q with
  | zero => exact linearIndependent_empty_type
  | succ q ih =>
    exact (linearIndependent_pow_mulVec_succ_iff A b q).2
      ⟨ih fun i hi => h i (Nat.lt_succ_of_lt hi), h q (Nat.lt_succ_self q)⟩

/-- Once `A^q b ∈ K_q`, the space `K_q` is `A`-invariant. -/
private lemma mulVec_mem_krylovSpace_of_pow_mulVec_mem {q : ℕ}
    (hq : (A ^ q) *ᵥ b ∈ krylovSpace A b q) {x : n → ℝ} (hx : x ∈ krylovSpace A b q) :
    A *ᵥ x ∈ krylovSpace A b q := by
  have h := mulVec_mem_krylovSpace_succ A b hx
  rw [krylovSpace_succ] at h
  exact (sup_le le_rfl ((Submodule.span_singleton_le_iff_mem _ _).2 hq)) h

/-- Once `A^q b ∈ K_q`, every `Aⁱ b` lies in `K_q`. -/
private lemma pow_mulVec_mem_of_pow_mulVec_mem {q : ℕ}
    (hq : (A ^ q) *ᵥ b ∈ krylovSpace A b q) (i : ℕ) : (A ^ i) *ᵥ b ∈ krylovSpace A b q := by
  induction i with
  | zero =>
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · exact hq
    · exact pow_mulVec_mem_krylovSpace A b hpos
  | succ i ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact mulVec_mem_krylovSpace_of_pow_mulVec_mem A b hq ih

/-- Once `A^q b ∈ K_q`, the span of all `Aⁱ b` is `K_q`. -/
private lemma span_range_eq_of_pow_mulVec_mem {q : ℕ}
    (hq : (A ^ q) *ᵥ b ∈ krylovSpace A b q) :
    Submodule.span ℝ (Set.range fun i : ℕ => (A ^ i) *ᵥ b) = krylovSpace A b q :=
  le_antisymm (Submodule.span_le.2 <| by
    rintro _ ⟨i, rfl⟩; exact pow_mulVec_mem_of_pow_mulVec_mem A b hq i)
    (krylovSpace_le_span_range A b q)

/-- Some power `A^q b` falls into the previous Krylov space (at the latest `q = card n`). -/
private lemma exists_pow_mulVec_mem : ∃ q, (A ^ q) *ᵥ b ∈ krylovSpace A b q := by
  by_contra hne
  push Not at hne
  have hli := linearIndependent_pow_mulVec_of_forall_not_mem A b
    (q := Fintype.card n + 1) fun i _ => hne i
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  omega

/-- The grade is the first index at which `A^q b` falls into `K_q`. -/
private lemma krylovGrade_eq_find [DecidablePred fun q => (A ^ q) *ᵥ b ∈ krylovSpace A b q] :
    krylovGrade A b = Nat.find (exists_pow_mulVec_mem A b) := by
  set ν := Nat.find (exists_pow_mulVec_mem A b)
  have hli := linearIndependent_pow_mulVec_of_forall_not_mem A b (q := ν)
    fun i hi => Nat.find_min (exists_pow_mulVec_mem A b) hi
  rw [krylovGrade, span_range_eq_of_pow_mulVec_mem A b (Nat.find_spec (exists_pow_mulVec_mem A b)),
    krylovSpace, finrank_span_eq_card hli, Fintype.card_fin]

/-- At the grade, `A^ν b` falls into `K_ν(A,b)`.
Source: Saad (2003) [`saad03`], Prop 6.2. Atlas: `krylov-grade`. -/
theorem pow_krylovGrade_mulVec_mem_krylovSpace :
    (A ^ krylovGrade A b) *ᵥ b ∈ krylovSpace A b (krylovGrade A b) := by
  classical
  rw [krylovGrade_eq_find]
  exact Nat.find_spec (exists_pow_mulVec_mem A b)

/-- Below the grade, `Aⁱ b` is not in `K_i(A,b)`.
Source: Saad (2003) [`saad03`], Prop 6.2. Atlas: `krylov-grade`. -/
theorem pow_mulVec_notMem_krylovSpace_of_lt_krylovGrade {i : ℕ} (hi : i < krylovGrade A b) :
    (A ^ i) *ᵥ b ∉ krylovSpace A b i := by
  classical
  rw [krylovGrade_eq_find] at hi
  exact Nat.find_min (exists_pow_mulVec_mem A b) hi

/-- The grade is at most any `q` with `A^q b ∈ K_q(A,b)`.
Source: Saad (2003) [`saad03`], Prop 6.2. Atlas: `krylov-grade`. -/
theorem krylovGrade_le_of_pow_mulVec_mem {q : ℕ} (hq : (A ^ q) *ᵥ b ∈ krylovSpace A b q) :
    krylovGrade A b ≤ q := by
  classical
  rw [krylovGrade_eq_find]
  exact Nat.find_min' _ hq

/-- The span of all `Aⁱ b` is `K_ν(A,b)`. Source: Saad (2003) [`saad03`], Prop 6.2.
Atlas: `krylov-grade`. -/
theorem span_range_pow_mulVec_eq_krylovSpace_krylovGrade :
    Submodule.span ℝ (Set.range fun i : ℕ => (A ^ i) *ᵥ b) =
      krylovSpace A b (krylovGrade A b) :=
  span_range_eq_of_pow_mulVec_mem A b (pow_krylovGrade_mulVec_mem_krylovSpace A b)

/-- Every power `Aⁱ b` lies in `K_ν(A,b)`. Source: Saad (2003) [`saad03`], Prop 6.2.
Atlas: `krylov-grade`. -/
theorem pow_mulVec_mem_krylovSpace_krylovGrade (i : ℕ) :
    (A ^ i) *ᵥ b ∈ krylovSpace A b (krylovGrade A b) :=
  pow_mulVec_mem_of_pow_mulVec_mem A b (pow_krylovGrade_mulVec_mem_krylovSpace A b) i

/-- Every Krylov space lies in `K_ν(A,b)`. Source: Saad (2003) [`saad03`], Prop 6.2.
Atlas: `krylov-grade`. -/
theorem krylovSpace_le_krylovSpace_krylovGrade (q : ℕ) :
    krylovSpace A b q ≤ krylovSpace A b (krylovGrade A b) :=
  (krylovSpace_le_span_range A b q).trans
    (span_range_pow_mulVec_eq_krylovSpace_krylovGrade A b).le

/-- **Invariance.** `K_ν(A,b)` is `A`-invariant: `x ∈ K_ν → A x ∈ K_ν`.
Source: Saad (2003) [`saad03`], Prop 6.2. Atlas: `krylov-grade` (partial: invariance).
atlas: krylov-grade (partial) -/
theorem mulVec_mem_krylovSpace_krylovGrade {x : n → ℝ}
    (hx : x ∈ krylovSpace A b (krylovGrade A b)) :
    A *ᵥ x ∈ krylovSpace A b (krylovGrade A b) :=
  mulVec_mem_krylovSpace_of_pow_mulVec_mem A b (pow_krylovGrade_mulVec_mem_krylovSpace A b) hx

/-- **Stabilisation.** Past the grade the Krylov spaces stop growing: `ν ≤ q → K_q = K_ν`.
Source: Saad (2003) [`saad03`], Prop 6.2. Atlas: `krylov-grade` (partial: stabilisation).
atlas: krylov-grade (partial) -/
theorem krylovSpace_eq_of_krylovGrade_le {q : ℕ} (h : krylovGrade A b ≤ q) :
    krylovSpace A b q = krylovSpace A b (krylovGrade A b) :=
  le_antisymm (krylovSpace_le_krylovSpace_krylovGrade A b q) (krylovSpace_mono A b h)

/-- **Breakdown criterion.** `b, Ab, …, A^(q−1) b` are linearly independent iff `q ≤ ν(A,b)`.
Source: Saad (2003) [`saad03`], Prop 6.1–6.2. Atlas: `krylov-grade` (partial: independence).
atlas: krylov-grade (partial) -/
theorem linearIndependent_pow_mulVec_iff_le_krylovGrade {q : ℕ} :
    LinearIndependent ℝ (fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b) ↔ q ≤ krylovGrade A b := by
  constructor
  · intro hli
    have h1 : Module.finrank ℝ (krylovSpace A b q) = q := by
      rw [krylovSpace, finrank_span_eq_card hli, Fintype.card_fin]
    calc q = Module.finrank ℝ (krylovSpace A b q) := h1.symm
      _ ≤ krylovGrade A b := Submodule.finrank_mono (krylovSpace_le_span_range A b q)
  · intro hq
    exact linearIndependent_pow_mulVec_of_forall_not_mem A b fun i hi =>
      pow_mulVec_notMem_krylovSpace_of_lt_krylovGrade A b (lt_of_lt_of_le hi hq)

/-- **Dimension of a Krylov space.** `dim K_q(A,b) = min q ν(A,b)`.
Source: Saad (2003) [`saad03`], Prop 6.3. Atlas: `krylov-grade` (partial: dimension).
atlas: krylov-grade (partial) -/
theorem finrank_krylovSpace (q : ℕ) :
    Module.finrank ℝ (krylovSpace A b q) = min q (krylovGrade A b) := by
  have hle : ∀ q ≤ krylovGrade A b, Module.finrank ℝ (krylovSpace A b q) = q := fun q hq => by
    rw [krylovSpace, finrank_span_eq_card
      ((linearIndependent_pow_mulVec_iff_le_krylovGrade A b).2 hq), Fintype.card_fin]
  rcases le_total q (krylovGrade A b) with h | h
  · rw [hle q h, min_eq_left h]
  · rw [krylovSpace_eq_of_krylovGrade_le A b h, hle _ le_rfl, min_eq_right h]

/-- The grade is at most the degree of the minimal polynomial of `A`.
Source: Saad (2003) [`saad03`], Prop 6.1 (`μ_{A,b} ∣ μ_A`). Atlas: `krylov-grade` (partial).
atlas: krylov-grade (partial) -/
theorem krylovGrade_le_natDegree_minpoly :
    krylovGrade A b ≤ (minpoly ℝ A).natDegree := by
  set p := minpoly ℝ A
  set m := p.natDegree
  have hint : IsIntegral ℝ A := Algebra.IsIntegral.isIntegral A
  have hmon : p.Monic := minpoly.monic hint
  have hpdeg : p.degree = m := degree_eq_natDegree hmon.ne_zero
  refine krylovGrade_le_of_pow_mulVec_mem A b (q := m) ?_
  have hdeg : (p - X ^ m).degree < (m : WithBot ℕ) := by
    rcases eq_or_ne (p - X ^ m) 0 with h0 | h0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    have h := degree_sub_lt_left (p := p) (q := X ^ m)
      (by rw [degree_X_pow, hpdeg]) hmon.ne_zero
      (by rw [hmon.leadingCoeff, leadingCoeff_X_pow])
    rwa [hpdeg] at h
  have hmem := (mem_krylovSpace_iff_degree A b m (-(aeval A (p - X ^ m) *ᵥ b))).2
    ⟨-(p - X ^ m), by rwa [degree_neg], by rw [map_neg, Matrix.neg_mulVec]⟩
  have hp : aeval A p = 0 := minpoly.aeval ℝ A
  rw [map_sub, hp, zero_sub, Matrix.neg_mulVec, neg_neg, map_pow, aeval_X] at hmem
  exact hmem

/-- The grade is at most the dimension: `ν(A,b) ≤ n`.
Source: Saad (2003) [`saad03`], Prop 6.1. Atlas: `krylov-grade` (partial).
atlas: krylov-grade (partial) -/
theorem krylovGrade_le_card : krylovGrade A b ≤ Fintype.card n :=
  (Submodule.finrank_le _).trans (Module.finrank_fintype_fun_eq_card ℝ).le

/-- The grade vanishes exactly for the zero vector: `ν(A,b) = 0 ↔ b = 0`.
Source: Liesen–Strakoš (2013) [`ls13`], §2.2. Atlas: `krylov-grade` (partial).
atlas: krylov-grade (partial) -/
theorem krylovGrade_eq_zero_iff : krylovGrade A b = 0 ↔ b = 0 := by
  constructor
  · intro h
    have hb := pow_krylovGrade_mulVec_mem_krylovSpace A b
    rw [h, krylovSpace_zero, Submodule.mem_bot, pow_zero, Matrix.one_mulVec] at hb
    exact hb
  · rintro rfl
    exact Nat.le_zero.1 (krylovGrade_le_of_pow_mulVec_mem A 0 (q := 0) (by simp))

/-- **Finite termination.** If `A` is invertible and `A x⋆ = c`, then for every `x₀` the error
`x⋆ − x₀` lies in `K_ν(A, r₀)`, `r₀ = c − A x₀`, `ν = ν(A, r₀)`; so every Krylov method that
minimises over `x₀ + K_q` is exact at `q = ν`. The proof: `A` maps the invariant space `K_ν`
injectively, hence onto, itself, and `r₀ = A (x⋆ − x₀)` lies in it.
Source: Saad (2003) [`saad03`], Prop 6.3 and §6.1 (`A⁻¹ b ∈ K_ν(A, b)`).
Atlas: `krylov-grade` (partial: finite termination).
atlas: krylov-grade (partial) -/
theorem sub_mem_krylovSpace_krylovGrade {A : Matrix n n ℝ} (hA : IsUnit A) {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) :
    xs - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) (krylovGrade A (c - A *ᵥ x₀)) := by
  set r := c - A *ᵥ x₀
  set K := krylovSpace A r (krylovGrade A r)
  have hr : r = A *ᵥ (xs - x₀) := by simp only [r, Matrix.mulVec_sub, hxs]
  have hrK : r ∈ K := by
    simpa using pow_mulVec_mem_krylovSpace_krylovGrade A r 0
  let f : K →ₗ[ℝ] K := (Matrix.mulVecLin A).restrict fun x hx =>
    mulVec_mem_krylovSpace_krylovGrade A r hx
  have hinjA : Function.Injective (Matrix.mulVec A) :=
    Matrix.mulVec_injective_iff_isUnit.2 hA
  have hinj : Function.Injective f := fun x y hxy =>
    Subtype.ext (hinjA (congrArg Subtype.val hxy))
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨r, hrK⟩
  have hy' : A *ᵥ (y : n → ℝ) = A *ᵥ (xs - x₀) := by
    rw [← hr]; exact congrArg Subtype.val hy
  rw [← hinjA hy']
  exact y.2

end NLAlib
