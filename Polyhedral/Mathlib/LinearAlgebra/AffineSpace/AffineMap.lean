import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

open Affine Module

section

variable {k : Type*} {V : Type*} {P : Type*} {V2 : Type*} {P2 : Type*}
  [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P] [AddCommGroup V2] [Module k V2] [AffineSpace V2 P2]

def AffineMap.range (f : P →ᵃ[k] P2) : AffineSubspace k P2 where
  carrier := Set.range f
  smul_vsub_vadd_mem := by
    simp only [Set.mem_range, forall_exists_index]
    intro c _ _ _ x₁ h₁ x₂ h₂ x₃ h₃
    exact ⟨c • (x₁ -ᵥ x₂) +ᵥ x₃, by simp [AffineMap.map_vadd, ← h₁, ← h₂, ← h₃]⟩

@[simp]
theorem AffineMap.mem_range (f : P →ᵃ[k] P2) (x : P2) : x ∈ f.range ↔ ∃ (y : P), f y = x :=
  Iff.rfl

open AffineMap Convexity

attribute [local instance] AddTorsor.toConvexSpace

variable [PartialOrder k] [IsStrictOrderedRing k]
lemma AffineMap.range_isConvexSet (f : P →ᵃ[k] P2) : IsConvexSet k (f.range : Set P2) := by
  simpa [range, SetLike.coe, ← Set.image_univ] using IsConvexSet.univ.image (f.isAffineMap)

end

-- open AffineMap in
-- theorem Convexity.IsConvexSet.preimage_isFaceOf {F C : PointedCone k W} (hf : F.IsFaceOf C)
--     (finj : Function.Injective f) :
--     ((IsConvexSet.pointedCone F).preimage f finj).IsFaceOf ((IsConvexSet.pointedCone C).preimage finj) where
--   subset := Set.preimage_mono (fun _ xm ↦ hf.le xm)
--   left_mem_of_mem_openSegment  := by
--     rintro x hx y hy z hz ⟨a, b, ha, hb, hab, hzo⟩
--     refine hf.mem_of_smul_add_mem hx (C.smul_mem hb.le hy) ha ?_
--     rwa [← convexCombPair_eq_smul_add_smul ha.le hb.le hab,
--       ←  f.isAffineMap.map_convexCombPair finj, hzo]
