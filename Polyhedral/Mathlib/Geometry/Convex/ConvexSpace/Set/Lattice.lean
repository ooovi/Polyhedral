module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Mathlib.Data.Fintype.Order

namespace Convexity

variable {ι R K X Y : Type*}

public section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]

variable (R X) in
/-- A bundled convex set. -/
structure ConvexSet where
  /-- The carrier set. -/
  carrier : Set X
  isConvexSet : IsConvexSet R carrier

namespace ConvexSet

instance : SetLike (ConvexSet R X) X where
  coe := ConvexSet.carrier
  coe_injective' K₁ K₂ _ := by cases K₁; cases K₂; congr

instance : PartialOrder (ConvexSet R X) := .ofSetLike ..

variable {K K₁ K₂ : ConvexSet R X}

variable (K) in
@[simp] lemma carrier_eq_coe : K.carrier = K := rfl

@[ext] theorem ext (h : ∀ x, x ∈ K₁ ↔ x ∈ K₂) : K₁ = K₂ := SetLike.ext h

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : ConvexSet R X) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : ConvexSet R X) = s := by ext; simp

example : (K₁ : Set X) ≤ K₂ ↔ K₁ ≤ K₂ := by simp [Set.le_eq_subset, SetLike.coe_subset_coe]

/-!
### Infimum, supremum and lattice
-/

/-- The infimum of two convex sets is a convex set. -/
instance : Min (ConvexSet R X) where
  min K₁ K₂ := ⟨_, K₁.isConvexSet.inter K₂.isConvexSet⟩

instance : SemilatticeInf (ConvexSet R X) where
  inf := min
  inf_le_left _ _ _ hx := hx.1
  inf_le_right _ _ _ hx := hx.2
  le_inf _ _ _ h₁₂ h₂₃ _ hx := ⟨h₁₂ hx, h₂₃ hx⟩

instance : InfSet (ConvexSet R X) where
  sInf S := ⟨sInf (SetLike.coe '' S), .sInter (by simpa using fun K _ => K.2)⟩

instance : CompleteSemilatticeInf (ConvexSet R X) where
  __ := instSemilatticeInf
  isGLB_sInf S := by
    constructor <;> intro L hL x hx
    · simp only [sInf, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, SetLike.mem_coe] at hx
      exact hx L hL
    · simp only [sInf, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, SetLike.mem_coe]
      exact fun l lS ↦ hL lS hx

instance : OrderBot (ConvexSet R X) where
  bot := ⟨∅, IsConvexSet.empty⟩
  bot_le _ _ hx := by simp at hx

instance : OrderTop (ConvexSet R X) where
  top := ⟨Set.univ, IsConvexSet.univ⟩
  le_top _ _ _ := by simp

instance : Inhabited (ConvexSet R X) := ⟨⊤⟩

variable {K K₁ K₂ : ConvexSet R X}

variable (R) in
/-- The convex hull of a set `s`, bundled as a `ConvexSet`. -/
def convexHull (s : Set X) : ConvexSet R X := ⟨Convexity.convexHull R s, .convexHull⟩

instance : Max (ConvexSet R X) where
  max K₁ K₂ := convexHull R (K₁ ∪ K₂)

lemma sup_eq_convexHull_union : (K₁ ⊔ K₂).carrier = Convexity.convexHull R (K₁ ∪ K₂) := by rfl

instance : SemilatticeSup (ConvexSet R X) where
  sup := max
  le_sup_left _ _ _ hs := by
    apply subset_convexHull_self
    simp [hs]
  le_sup_right _ _ _ hs := by
    apply subset_convexHull_self
    simp [hs]
  sup_le K₁ K₂ K₃ h₁₂ h₂₃ x hx := by
    rw [mem_mk, sup_eq_convexHull_union, mem_convexHull_iff] at hx
    refine hx K₃ ?_ K₃.isConvexSet
    simp [h₂₃, h₁₂]

instance : SupSet (ConvexSet R X) where
  sSup S := convexHull R (⋃ s ∈ S, s)

instance : CompleteSemilatticeSup (ConvexSet R X) where
  __ := instSemilatticeSup
  isLUB_sSup K := by
    constructor <;> intro L hL
    · intro l hl
      exact (Set.subset_iUnion₂_of_subset _ hL fun ⦃_⦄ a ↦ a).trans subset_convexHull_self hl
    · simp only [sSup, convexHull, convexHull, Convexity.convexHull,
        ClosureOperator.ofCompletePred_apply, Set.le_eq_subset, Set.iInf_eq_iInter]
      intro x xm
      simp only [mem_mk, Set.mem_iInter, Subtype.forall, Set.iUnion_subset_iff, and_imp] at xm
      exact xm _ hL L.isConvexSet

end ConvexSet

end Semiring

end Convexity
