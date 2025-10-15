import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Dual

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

namespace PointedCone

open Module LinearMap

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

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

alias coe_dual := dual_eq_submodule_dual

-- TODO: Replace `dual_span`
@[simp] lemma dual_span' (s : Set M) : dual p (span R s) = dual p s := dual_span ..

@[simp low + 1] lemma mem_dual'_singleton {x : M} {y : N} : y ∈ dual p {x} ↔ 0 ≤ p x y := by simp


lemma dual_subset {s t : Set M} (hst : s ⊆ t) : dual p t ≤ dual p s := by
  intro x hx
  rw [mem_dual] at *
  intro y hy
  exact hx (hst hy)

lemma dual_lineal (C : PointedCone R M) : dual p C.lineal = span R (dual p C) := sorry

section Map

open Module

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M']
  [AddCommGroup N'] [Module R N']

-- TODO: generalize to arbitrary pairings
lemma dual_map (f : M →ₗ[R] M') (s : Set M) :
    comap f.dualMap (dual (Dual.eval R M) s) = dual (Dual.eval R M') (f '' s) := by
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

example /- dual_inf -/ (C C' : PointedCone R M) :
    dual p (C ⊓ C' : PointedCone R M) = dual p (C ∩ C') := rfl
example (C C' : PointedCone R M) : dual p (C ⊔ C') = dual p (C ∪ C') := rfl

lemma dual_sup (C C' : PointedCone R M) : dual p (C ⊔ C' : PointedCone R M) = dual p (C ∪ C')
  := by nth_rw 2 [←dual_span]; simp

-- TODO: simp lemma?
lemma dual_sup_dual_inf_dual (C C' : PointedCone R M) :
    dual p (C ⊔ C' : PointedCone R M) = dual p C ⊓ dual p C' := by rw [dual_sup, dual_union]

-- TODO: Does this even hold in general? Certainly if C and C' are CoFG.
-- @[simp] lemma dual_flip_dual_union
example {C C' : PointedCone R M} : -- (hC : C.FG) (hC' : C'.FG) :
    dual p.flip (dual p (C ∪ C')) = C ⊔ C' := by
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

end PointedCone
