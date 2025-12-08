/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Partition.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Faces2
import Polyhedral.Hyperplane
import Polyhedral.Halfspace

open Module

-- ## PREDICATE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

-- TODO: can we reduce assumptions?
variable (p) [Fact (Function.Surjective p.flip)] in
lemma IsFaceOf.FG.subdual_subdual (hC : C.FG) (hF : F.IsFaceOf C) :
    subdual p.flip (dual p C) (subdual p C F) = F := by
  repeat rw [subdual_def]
  rw [FG.dual_flip_dual p hC]
  rw [← dual_span_lineal_dual]
  rw [Submodule.coe_inf, Submodule.coe_restrictScalars]
  nth_rw 3 [← PointedCone.ofSubmodule_coe]
  rw [FGDual.dual_inf_dual_sup_dual ?_ ?_]
  · rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]
    rw [FG.dual_flip_dual p hC]
    nth_rw 2 [← Submodule.dual_span]
    rw [Submodule.dual_flip_dual p]
    have H : (C ⊔ F.linSpan).lineal = F.linSpan := by
      sorry
    rw [H]
    exact IsFaceOf.inf_submodule hF
  · simpa using FG.dual_fgdual _ hC
  · rw [LinearMap.flip_flip, coe_fgdual_iff, ← Submodule.dual_span]
    exact Submodule.FG.dual_fgdual _ (submodule_span_fg <| hF.fg_of_fg hC)

-- TODO: can we reduce assumptions?
-- variable (p) [Fact p.SeparatingLeft] in
-- lemma IsFaceOf.FG.subdual_subdual' (hC : C.FG) (hF : F.IsFaceOf C) :
--     subdual p.flip (dual p C) (subdual p C F) = F := by
--   wlog _ : Module.Finite R M with exposed -- reduction to finite dimensional case
--   · sorry
--   repeat rw [subdual_def]
--   rw [FG.dual_flip_dual p hC]
--   rw [← dual_span_lineal_dual]
--   rw [Submodule.coe_inf, Submodule.coe_restrictScalars]
--   nth_rw 3 [← PointedCone.ofSubmodule_coe]
--   rw [FGDual.dual_inf_dual_sup_dual ?_ ?_]
--   · rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]
--     rw [FG.dual_flip_dual p hC]
--     nth_rw 2 [← Submodule.dual_span]
--     rw [Submodule.dual_flip_dual p]
--     have H : (C ⊔ F.linSpan).lineal = F.linSpan := by
--       sorry
--     rw [H]
--     exact IsFaceOf.inf_submodule hF
--   · simpa using FG.dual_fgdual _ hC
--   · rw [LinearMap.flip_flip, coe_fgdual_iff, ← Submodule.dual_span]
--     exact Submodule.FG.dual_fgdual _ (submodule_span_fg <| hF.fg_of_fg hC)


/-- Every face of an FG cone is exposed. -/
lemma IsFaceOf.FG.exposed (hC : C.FG) (hF : F.IsFaceOf C) :
    F.IsExposedFaceOf C := by
  wlog _ : Module.Finite R M with exposed -- reduction to finite dimensional case
  · let S : Submodule R M := .span R C
    have H := exposed (FG.restrict_fg S hC) (restrict S hF)
      (Finite.iff_fg.mpr <| submodule_span_fg hC)
    have hC : C ≤ Submodule.span R (C : Set M) := Submodule.le_span
    simpa [S, hC, le_trans hF.le hC] using H.embed
  rw [← FG.dual_flip_dual (Dual.eval R M) hC]
  rw [← subdual_subdual (Dual.eval R M) hC hF]
  exact .subdual_dual _ <| .subdual_dual _ hF

end PointedCone








-- ## BUNDLES STRUCTURE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

variable (hC : C.FG)



-- lemma Face.dual_dual (F : Face C) : dual p.flip (dual p F) = F := sorry


-- ## RANK

noncomputable def Face.rank (F : Face C) := Module.rank R F.span

-- def Face.IsRay (F : Face C) := F.rank = 1

-- lemma isAtom_of_isRay {F : Face C} (h : F.IsRay) : IsAtom F := sorry

-- def atoms : Set (Face C) := {F : Face C | IsAtom F}
-- def rays : Set (Face C) := {F : Face C | F.IsRay}

-- def coatoms : Set (Face C) := {F : Face C | IsCoatom F}
-- alias facets := coatoms


-- ## KREIN MILMAN

lemma atomic_of_fg (hC : C.FG) : IsAtomic (Face C) := sorry

lemma atomistic_of_fg (hC : C.FG) : IsAtomistic (Face C) := sorry

lemma coatomic_of_fg (hC : C.FG) : IsCoatomic (Face C) := sorry

lemma coatomistic_of_fg (hC : C.FG) : IsCoatomistic (Face C) := sorry

lemma face_complemented (hC : C.FG) : ComplementedLattice (Face C) := sorry

end PointedCone
