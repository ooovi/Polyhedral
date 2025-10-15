/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-- -/
import Mathlib.Analysis.Convex.Extreme
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic


/-!
# Faces of pointed cones

-/

namespace PointedCone

variable {𝕜 M N : Type*}

section Semiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]

abbrev IsFaceOf (F C : PointedCone 𝕜 M) := IsExtreme 𝕜 (E := M) C F

variable {C F F₁ F₂ : PointedCone 𝕜 M}

abbrev IsFaceOf.rfl : C.IsFaceOf C := IsExtreme.rfl

/-- A face of a pointed cone `C` is a pointed cone that is an extreme subset of `C`. -/
structure Face (C : PointedCone 𝕜 M) extends PointedCone 𝕜 M where
  isExtreme : IsExtreme (E := M) 𝕜 C toSubmodule

def of_IsFaceOf (hF : F.IsFaceOf C) : Face C := ⟨F, hF⟩

@[coe]
def Face.toPointedCone {C : PointedCone 𝕜 M} (f : Face C) := f.toSubmodule

instance : LE (Face C) := ⟨ fun F F' => F.toPointedCone ≤ F'.toPointedCone ⟩

abbrev Face.le (F : Face C) : F.toSubmodule ≤ C := F.isExtreme.subset

/-- The supremum of two faces `F₁, F₂` of `C` is the smallest face of `C` that has both `F₁` and
`F₂` as faces. -/
def Face.sup (F₁ : Face C) (F₂ : Face C) :=
  sInf { F : PointedCone 𝕜 M | F.IsFaceOf C ∧ F₁.toPointedCone ≤ F ∧ F₂.toPointedCone ≤ F}

lemma IsFaceOf.sup (F₁ : Face C) (F₂ : Face C) :
    (Face.sup F₁ F₂).IsFaceOf C := by
  unfold Face.sup
  constructor
  · intros _ sm
    simp at sm ⊢
    exact sm C rfl F₁.le F₂.le
  · simp; intros _ xc _ yc _ zfs zo F FFs FF₁ FF₂
    exact FFs.left_mem_of_mem_openSegment xc yc (zfs F FFs FF₁ FF₂) zo

end Semiring

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

    simp [openSegment] at zop
    obtain ⟨a, a0, b, b0, ab1, zab⟩ := zop

    have := congrArg Neg.neg zab
    rw [neg_add, ← smul_neg a] at this
    apply eq_sub_of_add_eq at this
    rw [sub_neg_eq_add] at this
    have : a • -x ∈ C := by rw [this]; exact C.add_mem zlin.2 (C.smul_mem (le_of_lt b0) yC)
    apply C.smul_mem (r := a⁻¹) (inv_nonneg_of_nonneg (G₀ := 𝕜) <| le_of_lt a0) at this
    rw [smul_comm, ← mul_smul, Field.mul_inv_cancel a (ne_of_lt a0).symm, one_smul 𝕜 (-x)] at this

    exact ⟨xC, this⟩

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


instance (C : PointedCone 𝕜 M) : Bot (Face C) := ⟨of_IsFaceOf <| .lineal⟩
instance (C : PointedCone 𝕜 M) : Top (Face C) := ⟨of_IsFaceOf <| .rfl⟩

instance (C : PointedCone 𝕜 M) : Min (Face C) where
  min F₁ F₂ := of_IsFaceOf <| .sup F₁ F₂

variable [AddCommGroup N] [Module 𝕜 N] (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair] in
instance (C : PointedCone 𝕜 M) : Max (Face C) where
  max F₁ F₂ := of_IsFaceOf <| .sup F₁ F₂

-- instance {C : PolyhedralCone 𝕜 M} : Coe (Face C) (PolyhedralCone 𝕜 M) := sorry

end Field

end PointedCone
