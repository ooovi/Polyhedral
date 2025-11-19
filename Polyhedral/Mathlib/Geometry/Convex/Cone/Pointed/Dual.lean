import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Dual

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal

namespace PointedCone

open Module LinearMap

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

-- `PointedCone.map` should be an abbrev

alias dual_bot := dual_zero

-- TODO: are there instances missing that should make the proof automatic?
-- TODO: 0 in `dual_univ` simplifies to ⊥, so maybe it is not the best statement?
@[simp] lemma dual_top [p.IsPerfPair] : dual p .univ = ⊥
  := dual_univ (IsPerfPair.bijective_right p).1

variable (p) in
@[simp] lemma dual_eq_submodule_dual (S : Submodule R M) : dual p S = Submodule.dual p S := by
  ext x; constructor
  · intro h _ ha
    have h' := h (neg_mem_iff.mpr ha)
    simp only [LinearMap.map_neg, neg_apply, Left.nonneg_neg_iff] at h'
    exact le_antisymm (h ha) h'
  · intro h _ ha
    rw [h ha]

alias coe_dual := dual_eq_submodule_dual

@[simp]
lemma dual_coe_coe_eq_dual_coe (S : Submodule R M) : dual p (S : PointedCone R M) = dual p S := by
  rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]

-- TODO: Replace `dual_span` in Cone/Dual.lean
@[simp] lemma dual_span' (s : Set M) : dual p (span R s) = dual p s := dual_span ..

@[simp low + 1] lemma mem_dual'_singleton {x : M} {y : N} : y ∈ dual p {x} ↔ 0 ≤ p x y := by simp

alias dual_antitone := dual_le_dual

variable (p) in
/-- Any cone is a subcone of its double dual cone. -/
lemma dual_dual_mono {s t : Set M} (hST : s ⊆ t) :
    dual p.flip (dual p s) ≤ dual p.flip (dual p t) := by
  exact dual_antitone <| dual_antitone hST

lemma le_dual_of_le_dual {S : PointedCone R M} {T : PointedCone R N}
    (hST : T ≤ dual p S) : S ≤ dual p.flip T :=
  le_trans subset_dual_dual (dual_antitone hST)

-- NOTE: This is the characterizing property of an antitone GaloisConnection.
lemma dual_le_iff_dual_le {S : PointedCone R M} {T : PointedCone R N} :
    S ≤ dual p.flip T ↔ T ≤ dual p S := ⟨le_dual_of_le_dual, le_dual_of_le_dual⟩

-- lemma span_sSup_sInf_span (S : Set (PointedCone R M)) :
--     span R (sSup S : PointedCone R M) = sInf {span R (E:=M) C | C ∈ S} := by
--   sorry

-- lemma dual_sSup' (S : Set (Set M)) :
--     dual p (sSup S) = dual p (⋃ C ∈ S, C) := by
--   rw [← dual_span, span, Submodule.span_sSup, dual_span]

@[simp] lemma dual_submodule_span (s : Set M) :
    dual p (Submodule.span R s) = Submodule.dual p s := by
  ext x; simp

@[simp] lemma submodule_dual_span (s : Set M) :
    Submodule.dual p (span R s) = Submodule.dual p s := by
  rw [← Submodule.dual_span]; simp

-- NOT TRUE
example (s : Set M) : Submodule.span R (dual p s : Set N) = Submodule.dual p s := by sorry

lemma dual_sSup (S : Set (PointedCone R M)) :
    dual p (⋃ C ∈ S, C) = dual p (sSup S : PointedCone R M) := by
  rw [← dual_span, span, Submodule.span_biUnion]

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

/-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual.
  For the other direction, see `IsDualClosed.dual_lineal_span_dual`. -/
lemma span_dual_le_dual_lineal {C : PointedCone R M} :
    Submodule.span R (dual p C) ≤ Submodule.dual p C.lineal := by
  simp only [Submodule.span, lineal, Submodule.dual_sSup_sInf_dual]
  refine sInf_le_sInf ?_
  intro T
  simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
  intro h
  obtain ⟨S, hSC, hS⟩ := h
  rw [← hS]
  nth_rw 3 [← ofSubmodule_coe]
  rw [SetLike.coe_subset_coe, ← dual_eq_submodule_dual]
  exact dual_le_dual hSC

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
  simp only [Submodule.mem_neg, mem_dual, _root_.map_neg, Left.nonneg_neg_iff,
    Set.involutiveNeg, Set.mem_neg]
  constructor
  · intro hy y hy'
    specialize hy hy'
    simp_all only [LinearMap.map_neg, LinearMap.neg_apply, Left.neg_nonpos_iff]
  · intro hy y hy'
    rw [← _root_.neg_neg y] at hy'
    specialize hy hy'
    simp_all only [_root_.neg_neg, LinearMap.map_neg, LinearMap.neg_apply, Left.nonneg_neg_iff]

lemma dual_id (s : Set M) : dual p s = dual .id (p '' s) := by ext x; simp

lemma dual_id_map (C : PointedCone R M) : dual p C = dual .id (map p C) := by ext x; simp

example /- dual_inf -/ (C D : PointedCone R M) :
    dual p (C ⊓ D : PointedCone R M) = dual p (C ∩ D) := rfl
example (C D : PointedCone R M) : dual p (C ⊔ D) = dual p (C ∪ D) := rfl

lemma dual_sup (C D : PointedCone R M) : dual p (C ⊔ D : PointedCone R M) = dual p (C ∪ D)
  := by nth_rw 2 [←dual_span]; simp

alias dual_sup_dual_union := dual_sup

-- TODO: simp lemma?
lemma dual_sup_dual_inf_dual (C D : PointedCone R M) :
    dual p (C ⊔ D : PointedCone R M) = dual p C ⊓ dual p D := by rw [dual_sup, dual_union]

-- TODO: Does this even hold in general? Certainly if C and D are CoFG.
-- @[simp] lemma dual_flip_dual_union
example {C D : PointedCone R M} : -- (hC : C.FG) (hC' : D.FG) :
    dual p.flip (dual p (C ∪ D)) = C ⊔ D := by
  sorry

--------------

lemma submodule_dual_le_dual {s : Set M} : Submodule.dual p s ≤ dual p s := by
  sorry --  rw [← submodule_span_dual]; exact Submodule.subset_span



-------------

-- ## Neg

lemma dual_neg (s : Set M) : -dual p s = dual p (-s) := by ext x; simp

@[simp] lemma dual_neg_neg (s : Set M) : -dual p (-s) = dual p s := by ext x; simp

-----------

section LinearOrder

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

lemma dual_span_lineal_dual (s : Set M) :
    (dual p s).lineal = Submodule.dual p s := by
  rw [Eq.comm]
  rw [← ofSubmodule_inj]
  rw [← dual_submodule_span]
  rw [← PointedCone.ofSubmodule_coe]
  rw [← span_union_neg_eq_span_submodule]
  rw [Set.involutiveNeg, dual_span]
  rw [dual_union]
  rw [← dual_neg, lineal_inf_neg]
  try rw [inf_comm]

-- lemma dual_span_lineal_dual' (C : PointedCone R M) :
--     Submodule.dual p (Submodule.span R (C : Set M)) = (dual p C).lineal := by
--   rw [← ofSubmodule_inj]
--   rw [← dual_eq_submodule_dual]
--   rw [← PointedCone.ofSubmodule_coe]
--   rw [← sup_neg_eq_submodule_span]
--   rw [dual_sup_dual_inf_dual]
--   rw [Submodule.coe_set_neg]
--   rw [← dual_neg, lineal_inf_neg]

end LinearOrder




---------------

variable (p) in
abbrev IsDualClosed (C : PointedCone R M) := dual p.flip (dual p C) = C

/-- A cone is bipolar if it is equal to its double dual. -/
-- Potentially the more canonical name for `IsDualClosed`.
alias IsBipolar := IsDualClosed

variable (p) in
@[simp] lemma IsDualClosed.def {C : PointedCone R M} (hC : IsDualClosed p C) :
     dual p.flip (dual p C) = C := hC

variable (p) in
@[simp] lemma IsDualClosed.def_flip {C : PointedCone R N} (hC : IsDualClosed p.flip C) :
     dual p (dual p.flip C) = C := hC

lemma IsDualClosed.def_iff {C : PointedCone R M} :
    IsDualClosed p C ↔ dual p.flip (dual p C) = C := by rfl

lemma IsDualClosed.def_flip_iff {C : PointedCone R N} :
    IsDualClosed p.flip C ↔ dual p (dual p.flip C) = C := by rfl

lemma IsDualClosed.coe_iff {S : Submodule R M} :
    IsDualClosed p S ↔ S.IsDualClosed p := sorry

lemma isDualClosed_coe {S : Submodule R M} (hS : S.IsDualClosed p) :
    IsDualClosed p S := IsDualClosed.coe_iff.mpr hS

lemma isDualClosed_coe' {S : Submodule R M} (hS : IsDualClosed p S) :
    S.IsDualClosed p := IsDualClosed.coe_iff.mp hS

variable (p) in
lemma dual_isDualClosed (C : PointedCone R M) : (dual p C).IsDualClosed p.flip := by
  simp [IsDualClosed, dual_dual_flip_dual]

variable (p) in
lemma dual_flip_IsDualClosed (C : PointedCone R N) : (dual p.flip C).IsDualClosed p
    := dual_isDualClosed p.flip C

lemma IsDualClosed.dual_inj {C D : PointedCone R M} (hC : C.IsDualClosed p) (hD : D.IsDualClosed p)
    (hCD : dual p C = dual p D) : C = D := by
  rw [← hC, ← hD, hCD]

@[simp] lemma IsDualClosed.dual_inj_iff {C D : PointedCone R M} (hC : C.IsDualClosed p)
    (hD : D.IsDualClosed p) : dual p C = dual p D ↔ C = D := ⟨dual_inj hC hD, by intro h; congr ⟩

lemma IsDualClosed.exists_of_dual_flip {C : PointedCone R M} (hC : C.IsDualClosed p) :
    ∃ D : PointedCone R N, D.IsDualClosed p.flip ∧ dual p.flip D = C
  := ⟨dual p C, by simp [IsDualClosed, hC.def]⟩

lemma IsDualClosed.exists_of_dual {C : PointedCone R N} (hC : C.IsDualClosed p.flip) :
    ∃ D : PointedCone R M, D.IsDualClosed p ∧ dual p D = C
  := hC.exists_of_dual_flip

lemma IsDualClosed.inf {S T : PointedCone R M} (hS : S.IsDualClosed p) (hT : T.IsDualClosed p) :
    (S ⊓ T).IsDualClosed p := by
  rw [← hS, ← hT, IsDualClosed, ← dual_sup_dual_inf_dual, dual_flip_dual_dual_flip]

theorem IsDualClosed.eq_sInf {C : PointedCone R M} (hC : C.IsDualClosed p) :
    C = sInf { D : PointedCone R M | D.IsDualClosed p ∧ C ≤ D } := by
  rw [Eq.comm, le_antisymm_iff]
  constructor
  · exact sInf_le ⟨hC, by simp⟩
  simp only [SetLike.le_def, Submodule.mem_sInf, Set.mem_setOf_eq, and_imp]
  intro x hx D hD hsD
  rw [← hD]; rw [← hC] at hx
  exact (dual_dual_mono p hsD) hx

lemma IsDualClosed.dual_le_of_dual_le {C : PointedCone R M} {D : PointedCone R N}
    (hC : C.IsDualClosed p) (hCD : dual p C ≤ D) : dual p.flip D ≤ C := by
  rw [← hC]; exact dual_antitone hCD

-- NOTE: This is the characterizing property of an antitone GaloisConnection.
lemma dual_le_iff_dual_le_of_isDualClosed {C : PointedCone R M} {D : PointedCone R N}
    (hC : C.IsDualClosed p) (hD : D.IsDualClosed p.flip) :
      dual p C ≤ D ↔ dual p.flip D ≤ C
    := ⟨hC.dual_le_of_dual_le, hD.dual_le_of_dual_le⟩

---------------

variable (p) in
lemma dual_dual_eval_le_dual_dual_bilin (s : Set M) :
    dual .id (dual (Dual.eval R M) s) ≤ dual p.flip (dual p s)
  := fun _ hx y hy => @hx (p.flip y) hy

lemma IsDualClosed.to_eval {S : PointedCone R M} (hS : S.IsDualClosed p)
    : S.IsDualClosed (Dual.eval R M) := by
  have h := dual_dual_eval_le_dual_dual_bilin p S
  rw [hS] at h
  exact le_antisymm h subset_dual_dual

---------------

lemma IsDualClosed.submodule_span_isDualClosed {C : PointedCone R M} (hC : C.IsDualClosed p) :
    (Submodule.span R C).IsDualClosed p := by
  unfold Submodule.IsDualClosed
  simp
  rw [← hC]
  --simp only [submodule_span_dual, submodule_dual_flip_dual]
  sorry

section LinearOrder

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

/-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual. -/
lemma IsDualClosed.dual_lineal_span_dual {C : PointedCone R M} (hC : C.IsDualClosed p) :
    Submodule.dual p C.lineal = Submodule.span R (dual p C) := by
  rw [← hC, dual_span_lineal_dual]
  nth_rw 1 [← flip_flip p]
  nth_rw 2 [← Submodule.dual_span]
  rw [(dual_isDualClosed p C).submodule_span_isDualClosed, dual_dual_flip_dual]

---------------

-- ## FARKAS

variable (p) in
lemma farkas (C : PointedCone R M) (hC : C.IsDualClosed p) (x : M) :
    x ∈ C ∨ ∃ φ : N, p x φ < 0 ∧ ∀ y ∈ C, 0 ≤ p y φ := by
  by_cases h : x ∈ C
  case pos => left; exact h
  case neg =>
    right
    rw [← hC.def] at h
    simp only [mem_dual, SetLike.mem_coe, flip_apply, not_forall, not_le] at h
    obtain ⟨φ, _, _⟩ := h
    use φ

end LinearOrder

section Field

open Function

variable {R : Type*} [Field R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

-- Q: Do we need Field?
/-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual. -/
-- lemma IsDualClosed.dual_lineal_span_dual {C : PointedCone R M} (hC : C.IsDualClosed p) :
--     Submodule.dual p C.lineal = Submodule.span R (dual p C) := by
--   rw [Eq.comm, le_antisymm_iff]
--   constructor
--   · exact span_dual_le_dual_lineal
--   simp only [lineal, Submodule.dual_sSup_sInf_dual]
--   have hh := (dual_isDualClosed p C).submodule_span_isDualClosed
--   rw [hh.eq_sInf]
--   --rw [submodule_span_dual]
--   refine sInf_le_sInf ?_
--   intro T
--   simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
--   intro ⟨hdc, h⟩
--   use Submodule.dual p.flip T
--   constructor
--   · rw [← hC, ← dual_eq_submodule_dual]
--     exact dual_antitone h  -- (le_trans dual_le_submodule_dual h)
--   · exact hdc

-- variable [Fact (Surjective p)] in
-- /-- For a dual closed cone, the dual of the lineality space is the submodule span of the dual. -/
-- lemma IsDualClosed.dual_lineal_span_dual'' {C : PointedCone R M} (hC : C.IsDualClosed p) :
--     Submodule.dual p C.lineal = Submodule.span R (dual p C) := by
--   simp only [lineal, Submodule.dual_sSup_sInf_dual]
--   unfold Submodule.span
--   congr; ext T
--   simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
--   constructor
--   · intro h -- this direction needs neither Field nor dual closed
--     obtain ⟨S, hSC, hS⟩ := h
--     rw [← hS]
--     nth_rw 3 [← ofSubmodule_coe]
--     rw [SetLike.coe_subset_coe, ← dual_eq_submodule_dual]
--     exact dual_le_dual hSC
--   · intro h -- this direction needs Field and dual closed; maybe not Field
--     use Submodule.dual p.flip T
--     constructor
--     · rw [← hC, ← dual_eq_submodule_dual]
--       exact dual_antitone h
--     · exact T.isDualClosed p.flip

-- variable [Fact (Surjective p)] in
-- /-- For a dual closed cone, the dual of the submodule span is the lineality space of the dual. -/
-- lemma IsDualClosed.dual_span_lineal_dual {C : PointedCone R M} (hC : C.IsDualClosed p) :
--     .dual p (Submodule.span R (C : Set M)) = (dual p C).lineal := by

--   have h := hC.dual_lineal_span_dual.symm
--   obtain ⟨D, hD, rfl⟩ := hC.exists_of_dual_flip
--   --rw [IsDualClosed, flip_flip] at hD
--   rw [hD.def_flip] at *
--   simp at *

--   sorry


lemma IsDualClosed.dual_dual_lineal {C : PointedCone R M} (hC : C.IsDualClosed p) :
    Submodule.span R (dual p.flip (dual p C)) =
      Submodule.dual p.flip (Submodule.dual p (Submodule.span R (C : Set M))) := by
  sorry

lemma IsDualClosed.dual_dual_span {C : PointedCone R M} (hC : C.IsDualClosed p) :
    (dual p.flip (dual p C)).lineal = Submodule.dual p.flip (Submodule.dual p C.lineal) := by
  sorry

lemma IsDualClosed.lineal {C : PointedCone R M} (hC : C.IsDualClosed p) :
    C.lineal.IsDualClosed p := by
  sorry

variable (p) [Fact (Surjective p.flip)] in
/-- Every submodule of a vector space is dual closed. -/
lemma isDualClosed (S : Submodule R M) : IsDualClosed p S :=
    isDualClosed_coe <| S.isDualClosed p

end Field

end PointedCone
