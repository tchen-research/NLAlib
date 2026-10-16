import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Prod

/-!
# Coordinate functions on disjoint sums of finite sets

These explicit equivalences perform the finite bookkeeping needed when a
coefficient index is moved into a matrix row or column.
-/

noncomputable section
open scoped Classical
namespace Equiv

/-- Functions on a disjoint sum of finite subsets split into two ordinary
coordinate functions. -/
def finsetSumCoordinates {α β ι : Type*} (S : Finset α) (T : Finset β) :
    ((S.disjSum T) → ι) ≃ (S → ι) × (T → ι) where
  toFun x := (fun a => x ⟨Sum.inl a, by simpa using a.property⟩,
    fun b => x ⟨Sum.inr b, by simpa using b.property⟩)
  invFun x := fun a => match a with
    | ⟨Sum.inl a, ha⟩ => x.1 ⟨a, by simpa using ha⟩
    | ⟨Sum.inr b, hb⟩ => x.2 ⟨b, by simpa using hb⟩
  left_inv x := by
    funext a
    rcases a with ⟨a | b, h⟩ <;> rfl
  right_inv x := by
    apply Prod.ext <;> funext a <;> rfl

/-- The first coordinate function is literal restriction to the left summand. -/
@[simp] theorem finsetSumCoordinates_fst {α β ι : Type*}
    (S : Finset α) (T : Finset β) (x : S.disjSum T → ι) (a : S) :
    (finsetSumCoordinates S T x).1 a = x ⟨Sum.inl a, by simpa using a.property⟩ := rfl

/-- The second coordinate function is literal restriction to the right summand. -/
@[simp] theorem finsetSumCoordinates_snd {α β ι : Type*}
    (S : Finset α) (T : Finset β) (x : S.disjSum T → ι) (b : T) :
    (finsetSumCoordinates S T x).2 b = x ⟨Sum.inr b, by simpa using b.property⟩ := rfl

/-- A disjoint finite-set complement is taken separately in each summand. -/
theorem compl_finset_disjSum {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) :
    (S.disjSum T)ᶜ = Sᶜ.disjSum Tᶜ := by
  ext (a | b) <;> simp

/-- A coordinate subset with no right-summand mode has exactly its left
coordinate function; the empty function factor is unique. -/
def finsetSumEmptyCoordinates {α β ι : Type*} (S : Finset α) :
    ((S.disjSum (∅ : Finset β)) → ι) ≃ (S → ι) :=
  (finsetSumCoordinates S ∅).trans (Equiv.prodUnique _ _)

/-- A single extra coordinate mode splits off one scalar index. -/
def finsetSumOneCoordinates {α ι : Type*} (S : Finset α) :
    ((S.disjSum (Finset.univ : Finset Unit)) → ι) ≃ (S → ι) × ι :=
  (finsetSumCoordinates S Finset.univ).trans
    ((Equiv.refl _).prodCongr
      ((Equiv.arrowCongr (Equiv.subtypeUnivEquiv (Finset.mem_univ : ∀ u : Unit, u ∈ Finset.univ))
        (Equiv.refl ι)).trans (Equiv.funUnique Unit ι)))

/-- The complement of a subset with no new mode contains that new mode, which
therefore splits off as one freely varying coordinate. -/
def finsetSumEmptyComplementCoordinates {α ι : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) : (↥((S.disjSum (∅ : Finset Unit))ᶜ : Finset (α ⊕ Unit)) → ι) ≃
      (↥(Sᶜ : Finset α) → ι) × ι where
  toFun x := (fun a => x ⟨Sum.inl a, by
    simpa only [Finset.mem_compl, Finset.inl_mem_disjSum] using a.property⟩,
    x ⟨Sum.inr (), by simp⟩)
  invFun x := fun a => match a with
    | ⟨Sum.inl a, ha⟩ => x.1 ⟨a, by simpa using ha⟩
    | ⟨Sum.inr _, _⟩ => x.2
  left_inv x := by
    funext a
    rcases a with ⟨a | u, h⟩
    · rfl
    · cases u
      rfl
  right_inv x := by
    apply Prod.ext
    · funext a
      rfl
    · rfl

/-- The complement of a subset containing the new mode has only the old
complementary coordinates left. -/
def finsetSumOneComplementCoordinates {α ι : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) : (↥((S.disjSum (Finset.univ : Finset Unit))ᶜ : Finset (α ⊕ Unit)) → ι) ≃
      (↥(Sᶜ : Finset α) → ι) where
  toFun x := fun a => x ⟨Sum.inl a, by
    simpa only [Finset.mem_compl, Finset.inl_mem_disjSum] using a.property⟩
  invFun x := fun a => match a with
    | ⟨Sum.inl a, ha⟩ => x ⟨a, by simpa using ha⟩
    | ⟨Sum.inr _, h⟩ => False.elim (by simpa using h)
  left_inv x := by
    funext a
    rcases a with ⟨a | u, h⟩
    · rfl
    · exact False.elim (by simpa using h)
  right_inv x := by
    funext a
    rfl

end Equiv
