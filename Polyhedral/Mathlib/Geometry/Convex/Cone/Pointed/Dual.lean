import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Dual

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

namespace PointedCone

open Module LinearMap

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

alias dual_bot := dual_zero

-- TODO: are there instances missing that should make the proof automatic?
-- TODO: 0 in `dual_univ` simplifies to ⊥, so maybe it is not the best statement?
@[simp] lemma dual_top [p.IsPerfPair] : dual p .univ = ⊥
  := dual_univ (IsPerfPair.bijective_right p).1

@[simp]
lemma dual_eq_submodule_dual (S : Submodule R M) : dual p S = Submodule.dual p S := by
  ext x; constructor
  · intro h _ ha
    have h' := h (neg_mem_iff.mpr ha)
    simp only [map_neg, neg_apply, Left.nonneg_neg_iff] at h'
    exact le_antisymm (h ha) h'
  · intro h _ ha
    rw [h ha]

@[simp]
lemma dual_coe_coe_eq_dual_coe (S : Submodule R M) : dual p (S : PointedCone R M) = dual p S := by
  rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]

alias coe_dual := dual_eq_submodule_dual

-- TODO: Replace `dual_span` in Cone/Dual.lean
@[simp] lemma dual_span' (s : Set M) : dual p (span R s) = dual p s := dual_span ..

@[simp low + 1] lemma mem_dual'_singleton {x : M} {y : N} : y ∈ dual p {x} ↔ 0 ≤ p x y := by simp

alias dual_antimono := dual_le_dual

-- lemma span_sSup_sInf_span (S : Set (PointedCone R M)) :
--     span R (sSup S : PointedCone R M) = sInf {span R (E:=M) C | C ∈ S} := by
--   sorry

-- lemma dual_sSup' (S : Set (Set M)) :
--     dual p (sSup S) = dual p (⋃ C ∈ S, C) := by
--   rw [← dual_span, span, Submodule.span_sSup, dual_span]

@[simp] lemma submodule_span_dual (s : Set M) :
    Submodule.span R (dual p s) = Submodule.dual p s := sorry

@[simp] lemma dual_submodule_span (s : Set M) :
    dual p (Submodule.span R s) = Submodule.dual p s := sorry

@[simp] lemma submodule_dual_flip_dual (s : Set M) :
    Submodule.dual p.flip (dual p s) = Submodule.span R s := by sorry

@[simp] lemma dual_flip_submodule_dual (s : Set M) :
    dual p.flip (Submodule.dual p s) = Submodule.span R s := by sorry



lemma dual_sSup (S : Set (PointedCone R M)) :
    dual p (⋃ C ∈ S, C) = dual p (sSup S : PointedCone R M) := by
  rw [← dual_span, span, Submodule.span_sSup]

lemma span_sSup_coe (S : Set (PointedCone R M)) :
    span R (sSup S : PointedCone R M) = span R (sSup (SetLike.coe '' S)) := by
  simp
  sorry

example (S : Set (Set M)) : dual p (sSup S : Set M) = sInf (dual p '' S) := dual_sUnion S

lemma dual_sSup_sInf_dual (S : Set (PointedCone R M)) :
    -- dual p (sSup S : PointedCone R M) = sInf (dual p '' (SetLike.coe '' S)) := by
    dual p (sSup S : PointedCone R M) = sInf ((dual p ∘ SetLike.coe) '' S) := by
  simp
  rw [← dual_span]
  simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
  --rw [Submodule.coe_sInf]
  sorry

example (S : Submodule R M) : ((S : PointedCone R M) : Set M) = (S : Set M)
    := by simp only [ofSubmodule_coe]

lemma span_dual_le_dual_lineal (C : PointedCone R M):
    Submodule.span R (dual p C) ≤ Submodule.dual p C.lineal := by
  -- This should be provable without `Field` and `IsDualClosed`.
  -- see proof of `dual_lineal_span_dual` below.
  sorry

section Map

open Module

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M']
  [AddCommGroup N'] [Module R N']

-- TODO: generalize to arbitrary pairings
lemma dual_map (f : M →ₗ[R] M') (s : Set M) :
    comap f.dualMap (dual (Dual.eval R M) s) = dual (Dual.eval R M') (f '' s) := by
  ext x; simp

lemma dual_map' (f : M →ₗ[R] M') (C : PointedCone R M) :
    comap f.dualMap (dual (Dual.eval R M) C) = dual (Dual.eval R M') (map f C) := by
  ext x; simp

-- TODO: generalize to arbitrary pairings
-- lemma dual_map' (f : M →ₗ[R] M') (hf : Function.Injective f) (s : Set M) :
--     map f.dualMap.inverse (dual (Dual.eval R M) s) = dual (Dual.eval R M') (f '' s) := by
--   ext x; simp

end Map

@[simp]
lemma neg_dual {s : Set M} : -(dual p s) = dual p (-s) := by
  ext x -- TODO: make this proof an application of `map_dual`
  simp
  constructor
  · intro hy y hy'
    specialize hy hy'
    simp_all only [map_neg, LinearMap.neg_apply, Left.neg_nonpos_iff]
  · intro hy y hy'
    rw [← _root_.neg_neg y] at hy'
    specialize hy hy'
    simp_all only [_root_.neg_neg, map_neg, LinearMap.neg_apply, Left.nonneg_neg_iff]

lemma dual_id (s : Set M) : dual p s = dual .id (p '' s) := by ext x; simp

lemma dual_id_map (C : PointedCone R M) : dual p C = dual .id (map p C) := by ext x; simp

example /- dual_inf -/ (C D : PointedCone R M) :
    dual p (C ⊓ D : PointedCone R M) = dual p (C ∩ D) := rfl
example (C D : PointedCone R M) : dual p (C ⊔ D) = dual p (C ∪ D) := rfl

lemma dual_sup (C D : PointedCone R M) : dual p (C ⊔ D : PointedCone R M) = dual p (C ∪ D)
  := by nth_rw 2 [←dual_span]; simp

-- TODO: simp lemma?
lemma dual_sup_dual_inf_dual (C D : PointedCone R M) :
    dual p (C ⊔ D : PointedCone R M) = dual p C ⊓ dual p D := by rw [dual_sup, dual_union]

-- TODO: Does this even hold in general? Certainly if C and D are CoFG.
-- @[simp] lemma dual_flip_dual_union
example {C D : PointedCone R M} : -- (hC : C.FG) (hC' : D.FG) :
    dual p.flip (dual p (C ∪ D)) = C ⊔ D := by
  sorry


-- the other direction does not hold in general (consider a cone with lineality space and now
--  delete every points from that lineality space except for the origin).
--  It holds for FG (and CoFG?)
-- Q: do I need p.IsPerfPair?
lemma span_dual_eq_dual_lineal [p.IsPerfPair] (C : PointedCone R M) :
    Submodule.span R (dual p C) ≤ .dual p C.lineal := by
  -- simp [lineal_mem]
  -- C.lin ≤ C
  -- hence dual C ≤ dual C.lin
  -- hence span dual C ≤ span dual C.lin = dual C.lin
  sorry

---------------

variable (p) in
abbrev IsDualClosed (C : PointedCone R M) := dual p.flip (dual p C) = C

variable (p) in
@[simp] lemma IsDualClosed.def {S : PointedCone R M} (hS : IsDualClosed p S) :
     dual p.flip (dual p S) = S := hS

variable (p) in
@[simp] lemma IsDualClosed.def_flip {S : PointedCone R N} (hS : IsDualClosed p.flip S) :
     dual p (dual p.flip S) = S := hS

lemma IsDualClosed.def_iff {S : PointedCone R M} :
    IsDualClosed p S ↔ dual p.flip (dual p S) = S := by rfl

lemma IsDualClosed.def_flip_iff {S : PointedCone R N} :
    IsDualClosed p.flip S ↔ dual p (dual p.flip S) = S := by rfl

variable (p) in
lemma dual_IsDualClosed (S : PointedCone R M) : (dual p S).IsDualClosed p.flip := by
  simp [IsDualClosed, flip_flip, dual_dual_flip_dual]

variable (p) in
lemma dual_flip_IsDualClosed (S : PointedCone R N) : (dual p.flip S).IsDualClosed p
    := dual_IsDualClosed p.flip S

lemma IsDualClosed.dual_inj {S T : PointedCone R M} (hS : S.IsDualClosed p) (hT : T.IsDualClosed p)
    (hST : dual p S = dual p T) : S = T := by
  rw [← hS, ← hT, hST]

@[simp] lemma IsDualClosed.dual_inj_iff {S T : PointedCone R M} (hS : S.IsDualClosed p)
    (hT : T.IsDualClosed p) : dual p S = dual p T ↔ S = T := ⟨dual_inj hS hT, by intro h; congr ⟩

lemma IsDualClosed.exists_of_dual_flip {S : PointedCone R M} (hS : S.IsDualClosed p) :
    ∃ T : PointedCone R N, T.IsDualClosed p.flip ∧ dual p.flip T = S
  := ⟨dual p S, by simp [IsDualClosed, hS.def]⟩

lemma IsDualClosed.exists_of_dual {S : PointedCone R N} (hS : S.IsDualClosed p.flip) :
    ∃ T : PointedCone R M, T.IsDualClosed p ∧ dual p T = S := exists_of_dual_flip hS

---------------

section Field

variable {R : Type*} [Field R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

/-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual. -/
lemma IsDualClosed.dual_lineal_span_dual {C : PointedCone R M} (hC : C.IsDualClosed p) :
    Submodule.dual p C.lineal = Submodule.span R (dual p C) := by
  simp only [lineal, Submodule.span, Submodule.dual_sSup_sInf_dual, Function.comp_apply]
  congr; ext T
  rw [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro h -- this direction needs neither Field nor dual closed
    obtain ⟨S, hSC, hS⟩ := h
    rw [← hS]
    nth_rw 3 [← ofSubmodule_coe]
    rw [SetLike.coe_subset_coe, ← dual_eq_submodule_dual]
    exact dual_le_dual hSC
  · intro h -- this direction needs Field and dual closed; maybe not Field
    use Submodule.dual p.flip T
    constructor
    · rw [Set.mem_setOf_eq, ← hC, ← dual_eq_submodule_dual]
      exact dual_antimono h
    · exact T.isDualClosed p.flip

/-- For a dual closed cone, the dual of the submodule span is the lineality space of the dual. -/
lemma IsDualClosed.dual_span_lineal_dual {C : PointedCone R M} (hC : C.IsDualClosed p) :
    .dual p (Submodule.span R (C : Set M)) = (dual p C).lineal := by
  have h := hC.dual_lineal_span_dual.symm
  obtain ⟨D, hD, rfl⟩ := hC.exists_of_dual_flip
  --rw [IsDualClosed, flip_flip] at hD
  rw [hD.def_flip] at *
  simp at *
  sorry

end Field

end PointedCone
