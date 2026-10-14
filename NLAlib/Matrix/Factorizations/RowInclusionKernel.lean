import NLAlib.Matrix.Factorizations.LURowInclusion
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Fintype.BigOperators

/-!
# Row inclusion from leading kernel relations

A linear functional that vanishes on the common kernel of finitely many
linear functionals is in their span. This gives a field-general criterion
for the existing row-inclusion predicate, without assuming invertible pivots.
Source: Horn–Johnson (2013), Theorem 3.5.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {K n : Type*} [Field K] [Fintype n] [LinearOrder n]

/-- Leading null vectors determine row inclusion: every vector supported
strictly before a diagonal label whose leading output vanishes must also
have zero output at that label. This criterion applies over any field. -/
theorem hasRowInclusion_of_prefix_kernel {A : Matrix n n K}
    (hA : ∀ i : n, ∀ x : n → K, (∀ j : n, ¬j < i → x j = 0) →
      (∀ j : n, j < i → (A *ᵥ x) j = 0) → (A *ᵥ x) i = 0) :
    HasRowInclusion A := by
  intro i
  let I := {j : n // j < i}
  have hsum (f : I → K) :
      (∑ j : n, if h : j < i then f ⟨j, h⟩ else 0) = ∑ j : I, f j := by
    have hh := Fintype.sum_subtype_add_sum_subtype (fun j : n => j < i)
      (fun j => if h : j < i then f ⟨j, h⟩ else 0)
    have hleft : (∑ j : I, if h : (j : n) < i then f ⟨j, h⟩ else 0) = ∑ j : I, f j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [dif_pos j.property]
    have hright : (∑ j : {j : n // ¬j < i},
        if h : (j : n) < i then f ⟨j, h⟩ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [dif_neg j.property]
    rw [hleft, hright, add_zero] at hh
    exact hh.symm
  let L : I → (I → K) →ₗ[K] K := fun j => dotProductBilin K K (fun k : I => A j k)
  let T : (I → K) →ₗ[K] K := dotProductBilin K K (fun k : I => A i k)
  have hker : (⨅ j, LinearMap.ker (L j)) ≤ LinearMap.ker T := by
    intro x hx
    let y : n → K := fun k => if h : k < i then x ⟨k, h⟩ else 0
    have hy (k : n) : (A *ᵥ y) k = ∑ j : I, A k j * x j := by
      change (∑ j : n, A k j * y j) = _
      have heq : (fun j => A k j * y j) =
          fun j => if h : j < i then A k j * x ⟨j, h⟩ else 0 := by
        funext j
        dsimp only [y]
        split_ifs <;> simp
      rw [heq]
      exact hsum (fun j : I => A k j * x j)
    have hz : (A *ᵥ y) i = 0 := hA i y (fun j hj => by simp [y, hj]) (by
      intro j hj
      have hh := ((Submodule.mem_iInf _).mp hx) (⟨j, hj⟩ : I)
      rw [hy]
      exact hh)
    rw [hy] at hz
    exact hz
  have hT : T ∈ Submodule.span K (Set.range L) := mem_span_of_iInf_ker_le_ker hker
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hT
  let c₀ : n → K := fun j => if h : j < i then c ⟨j, h⟩ else 0
  refine ⟨c₀, fun j hj => by simp [c₀, hj], ?_⟩
  intro k hk
  have heval := congrArg (fun f : (I → K) →ₗ[K] K => f (Pi.single ⟨k, hk⟩ 1)) hc
  have hcoeff : (∑ j : I, c j * A j k) = A i k := by
    simpa [L, T, dotProductBilin, dotProduct_single_one] using heval
  have heq : (fun j : n => c₀ j * A j k) =
      fun j => if h : j < i then c ⟨j, h⟩ * A j k else 0 := by
    funext j
    dsimp only [c₀]
    split_ifs <;> simp
  rw [heq]
  exact hcoeff.symm.trans (hsum (fun j : I => c j * A j k)).symm

end NLAlib
