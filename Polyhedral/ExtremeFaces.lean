/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-- -/
import Mathlib.Analysis.Convex.Extreme
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual


/-!
# Faces of pointed cones

-/

namespace PointedCone

variable {𝕜 M N : Type*}

section Semiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]

abbrev IsFaceOf (F C : PointedCone 𝕜 M) := IsExtreme 𝕜 (E := M) C F

variable {C F F₁ F₂ : PointedCone 𝕜 M}

-- TODO does this make sense to have?
abbrev IsFaceOf.rfl : C.IsFaceOf C := IsExtreme.rfl

abbrev IsFaceOf.trans (h₁ : F₁.IsFaceOf F) (h₂ : F.IsFaceOf F₂) : F₁.IsFaceOf F₂ :=
  IsExtreme.trans h₂ h₁

abbrev IsFaceOf.inter (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C :=
  IsExtreme.inter h₁ h₂


/-- A face of a pointed cone `C` is a pointed cone that is an extreme subset of `C`. -/
structure Face (C : PointedCone 𝕜 M) extends PointedCone 𝕜 M where
  isFaceOf : IsFaceOf toSubmodule C

namespace Face

def of_IsFaceOf (hF : F.IsFaceOf C) : Face C := ⟨F, hF⟩

-- we can't have an actual Coe instance because coercion target throws away the information `C`
@[coe]
def toPointedCone {C : PointedCone 𝕜 M} (f : Face C) := f.toSubmodule

instance : CoeOut (Face (M := M) (𝕜 := 𝕜) C) (PointedCone 𝕜 M) where
coe f := f.toSubmodule

instance : CoeHead (Face (M := M) (𝕜 := 𝕜) C) (PointedCone 𝕜 M) where
coe f := f.toSubmodule

@[simp, norm_cast]
theorem toPointedCone_eq_iff {F₁ F₂ : Face C} :
    F₁.toPointedCone = F₂.toPointedCone ↔ F₁ = F₂ := by
  constructor <;> intro h <;> try rw [mk.injEq] at *; exact h


/-!
## Partial Order and Lattice on Faces

-/

-- maybe this is a better definition for lt
-- private lemma lt_iff_le_not_ge {F₁ F₂ : C.Face} :
--     IsFaceOf F₁.toPointedCone F₂.toPointedCone ∧ F₁ ≠ F₂ ↔
--     IsFaceOf F₁.toPointedCone F₂.toPointedCone ∧ ¬(IsFaceOf F₂.toPointedCone F₁.toPointedCone) := by
--   simp; intro hf
--   constructor <;> intro h <;> by_contra hc
--   · have := IsExtreme.antisymm hc hf
--     norm_cast at this
--   · rw [hc] at h
--     exact h IsExtreme.rfl

instance : PartialOrder (Face C) where
le F₁ F₂ := IsFaceOf F₁.toPointedCone F₂.toPointedCone
lt F₁ F₂ := IsFaceOf F₁.toPointedCone F₂.toPointedCone ∧
  ¬(IsFaceOf F₂.toPointedCone F₁.toPointedCone)
le_refl F := IsExtreme.rfl
le_trans F₁ F₂ F h₁ h₂ := IsExtreme.trans h₂ h₁
lt_iff_le_not_ge F C := by simp
le_antisymm F₁ F₂ h₁ h₂ := by convert IsExtreme.antisymm h₂ h₁; norm_cast

@[simp]
theorem toPointedCone_le {F₁ F₂ : Face C} (h : F₁ ≤ F₂) :
    F₁.toPointedCone ≤ F₂.toPointedCone := by
  intro x xF₁; simp [LE.le] at h; exact h.subset xF₁

abbrev le_all {F : Face C} : F.toSubmodule ≤ C := F.isFaceOf.subset

/-- The supremum of two faces `F₁, F₂` of `C` is the smallest face of `C` that has both `F₁` and
`F₂` as faces. -/
def sup (F₁ : Face C) (F₂ : Face C) : Face C := by
  refine ⟨sInf { F : PointedCone 𝕜 M | F.IsFaceOf C ∧ ↑F₁ ≤ F ∧ ↑F₂ ≤ F}, ?_⟩
  constructor
  · intros _ sm
    simp at sm ⊢
    exact sm C IsFaceOf.rfl F₁.le_all F₂.le_all
  · simp; intros _ xc _ yc _ zfs zo F FFs FF₁ FF₂
    exact FFs.left_mem_of_mem_openSegment xc yc (zfs F FFs FF₁ FF₂) zo

lemma sup.symm (F₁ F₂ : Face C) : sup F₁ F₂ = sup F₂ F₁ := by simp [sup, and_comm]

-- this is terrible
private lemma left_mem_of_mem_openSegment {F₁ F₂ : Face C} :
    ∀ ⦃x : M⦄, x ∈ SetLike.coe F₂.toPointedCone →
    ∀ ⦃y : M⦄, y ∈ SetLike.coe F₂.toPointedCone →
    ∀ ⦃z : M⦄, z ∈ SetLike.coe F₁.toPointedCone → z ∈ openSegment 𝕜 x y →
    x ∈ SetLike.coe F₁.toPointedCone := by
  intros _ asup _ bsup _ zF zo
  exact F₁.isFaceOf.left_mem_of_mem_openSegment (le_all asup) (le_all bsup) zF zo

instance : SemilatticeSup (Face C) where
sup := sup
le_sup_left F₁ F₂ := by
  constructor
  · simp only [SetLike.coe_subset_coe]; exact le_sInf (fun F' F's => F's.2.1)
  · exact left_mem_of_mem_openSegment
le_sup_right F₁ F₂ := by
  constructor
  · simp only [SetLike.coe_subset_coe]; exact le_sInf (fun F' F's => F's.2.2)
  · exact left_mem_of_mem_openSegment
sup_le F₁ F₂ F₃ f₁₂ f₂₃:= by
  constructor
  · intros x xs
    have : F₃.toPointedCone ∈ { F : PointedCone 𝕜 M | F.IsFaceOf C ∧ ↑F₁ ≤ F ∧ ↑F₂ ≤ F} :=
      ⟨F₃.isFaceOf, toPointedCone_le f₁₂, toPointedCone_le f₂₃⟩
    exact sInf_le this xs
  · exact left_mem_of_mem_openSegment

end Face

end Semiring



/-!
## Particular Faces

-/
section Field

variable [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]
  {C F F₁ F₂ : PointedCone 𝕜 M}

-- TODO moving this to Ring instead of Field entails disaster
lemma IsFaceOf.lineal : IsFaceOf C.lineal C := by
  constructor
  · exact PointedCone.lineal_le C
  · simp
    intros x xC y yC z zlin zop
    rw [lineal_mem] at zlin ⊢
    refine ⟨xC, ?_⟩

    simp [openSegment] at zop
    obtain ⟨a, a0, _, b0, _, zab⟩ := zop

    rw [← one_smul 𝕜 (-x), ← Field.mul_inv_cancel a (ne_of_lt a0).symm, mul_comm, mul_smul]
    apply C.smul_mem (r := a⁻¹) (inv_nonneg_of_nonneg (G₀ := 𝕜) <| le_of_lt a0)

    have := congrArg Neg.neg zab
    rw [neg_add, ← smul_neg a] at this
    apply eq_sub_of_add_eq at this
    rw [sub_neg_eq_add] at this
    rw [this]

    exact C.add_mem zlin.2 (C.smul_mem (le_of_lt b0) yC)

section Pair

variable [AddCommGroup N] [Module 𝕜 N] (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜)

def subdual (C F : PointedCone 𝕜 M) : PointedCone 𝕜 N := dual p F ⊓ dual p C

lemma IsFaceOf.subdual_dual (hF : F.IsFaceOf C) :
    (subdual p C F).IsFaceOf (dual p C) := by
  unfold subdual
  refine ⟨by simp, ?_⟩
  intros x xd
  suffices x ∈ dual p F by simp [this, xd]
  exact mem_dual.mpr <| fun _ xxf => xd <| hF.subset xxf

lemma subdual_inf_sup (C : PointedCone 𝕜 M) :
    subdual p C F₁ ⊓ subdual p C F₂ = subdual p C (F₁ ⊔ F₂) := by
    simp [subdual, inf_assoc]
    rw [← inf_assoc, dual_sup_dual_inf_dual]

lemma IsFaceOf.susub (h1 : F₁.IsFaceOf C) (h2 : F₂.IsFaceOf C) :
    (subdual .id (dual (Module.Dual.eval 𝕜 M) C)
  ((subdual (Module.Dual.eval 𝕜 M) C F₁) ⊓ (subdual (Module.Dual.eval 𝕜 M) C F₂))).IsFaceOf C := by
  -- constructor
  -- simp only [subdual, dual, SetLike.mem_coe, Module.Dual.eval_apply, Submodule.coe_inf,
  --   Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_inter_iff,
  --   Set.mem_setOf_eq, LinearMap.id_coe, id_eq, and_imp]
  -- intros y ys
  -- simp at ys
  -- sorry
  sorry

end Pair

namespace Face

instance (C : PointedCone 𝕜 M) : Bot (Face C) := ⟨of_IsFaceOf <| .lineal⟩
instance (C : PointedCone 𝕜 M) : Top (Face C) := ⟨of_IsFaceOf <| .rfl⟩

end Field

end PointedCone
