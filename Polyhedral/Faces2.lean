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

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Field
import Polyhedral.Faces
import Polyhedral.Halfspace

/-!
# Polyhedral cones

...
-/

/-
Next goal: **Polyhedral Cone decomposition**
 * Over a field every subspace is dual closed, which simplifies some of the below
 * dual closed subspaces are polyhedral cones
 * combiantorial equivalence
 * product face lattices
 * subspaces have only 1 face (and are the only dual closed ones with this property?)
 * if a face lattice is finite, then it is graded?
 * FG cones have graded face lattices
   * if F > G are faces and dim F > dim G + 1, then there is a face in between.
 * ∃ D : PolyhedralCone 𝕜 M, D.FG ∧ ∃ S : Submodule 𝕜 M, S.IsDualClosed .. ∧ D ⊔ S = C
   * choose S := C.lineal
   * take a subspace T complementary to S
   * set D := C ⊓ T
   * show D is FG
   * theorem: a dual closed cone with finitely many faces and no lineality is FG.
     * there are 1-dimensional faces.
     * idee: the 1-dim faces generate D (Krein-Milmann)
  * Are the following things true for dual closed cones with finite face lattice?
    * Every face is contained in a facet.
    * Every face contains a 1-face.
-/

/- # Strategy:
  * A halfspace has two faces (⊥ and ⊤)
  * Every dual closed cone with two faces (neccessarily ⊥ and ⊤) is a halfspace
  * every face in a halfspace is exposed
  * fibers of exposed faces are exposed
  * intersection of exposed faces is exposed
  * Assume now that C is a dual closed cone with finitely many faces
  * every face lies in a co-atom (just walk up until you find one)
  * Every co-atom is exposed
    * quotient by co-atom
    * the quotient has two faces --> is a halfspace
    * bottom face of halspace is exposed
    * fiber preserves exposed --> co-atom is exposed
  * ?? every face is exposed
    * ?? quotient of a dual closed cone is dual closed?
    * ?? bottom face of a dual closed cone is exposed
    * proceed by induction
      * quotient by any face F (bot face is special case)
      * quotient cone is dual-closed and has finite and smaller face lattice
      * by IH bottom face is exposed
      * fiber of bottom face is F, hence exposed
  * ?? every face is intersection of top face
-/

/- What else we need:
 * how faces transform under maps
   * images of faces are faces of the image (gives a face lattice isom)
   * ...
 * faces lattice of a face of C is a lower interval of face lattice of C
 * projection along a face gives a cone whose face lattice is an upper interval
   of the face lattice of C
 * duality flips the face lattice
 * intervals in a face lattice are a face lattice
 * exposed faces
   * bot and top are exposed
   * if there are finitely many faces, then all faces are exposed
 * projections with FG ker preserve dual closedness
   * how do projections behave under duality
-/

open Function Module OrderDual LinearMap
open Submodule hiding span dual IsDualClosed
open PointedCone


namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}

-- ## IMPORTANT

namespace Face

variable {F F₁ F₂ : Face C}

@[simp] lemma mem_toPointedCone (x : M) : x ∈ F ↔ x ∈ F.toPointedCone := .rfl

@[ext] lemma ext (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

end Face


-- ## MISC

lemma isFaceOf_def_iff :
    F.IsFaceOf C ↔ ∀ x ∈ C, ∀ y ∈ C, ∀ c : R, c > 0 → c • x + y ∈ F → x ∈ F := by sorry
    -- F.IsFaceOf C ↔ F ≤ C ∧ ∀ x ∈ C, ∀ y ∈ C, ∀ c : R, c > 0 → c • x + y ∈ F → x ∈ F := by sorry

/-- The linear span of the face. -/
abbrev Face.span (F : Face C) : Submodule R M := Submodule.span R F

lemma IsFaceOf.iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂ := by
  constructor
  · exact le_self
  rw [isFaceOf_def_iff] at ⊢ h₁
  exact fun _ x hx y hy => h₁ x (h₂.le_self hx) y (h₂.le_self hy)

lemma IsFaceOf.of_cone_iff_of_face (h₁ : F₁.IsFaceOf C) (h₂ : F₂ ≤ F₂) :
    F₂.IsFaceOf C ↔ F₂.IsFaceOf F₁ := sorry


-- ## DUAL

variable (p) in
/-- The face of the dual cone that corresponds to this face. -/
def Face.dual (F : Face C) : Face (dual p C) := ⟨_, F.isFaceOf.subdual_dual p⟩

lemma Face.dual_antitone : Antitone (dual p : Face C → Face _) := by
  sorry


-- ## RESTRICT / EMBED

lemma IsFaceOf.restrict (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    (F₁ ⊓ F₂).IsFaceOf F₁ := (h₁.of_cone_iff_of_face (le_refl _)).mp (h₁.inf h₂)

-- Change order of arguments in `IsFaceOf.trans` because currently inconsistent with `embed`?
alias IsFaceOf.embed := IsFaceOf.trans

def Face.restrict (F₁ F₂ : Face C) : Face (F₁ : PointedCone R M) :=
    ⟨F₁ ⊓ F₂, F₁.isFaceOf.restrict F₂.isFaceOf⟩

def Face.embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : Face C :=
    ⟨F₂, F₂.isFaceOf.trans F₁.isFaceOf⟩

/-- A face of a face of C coerces to a face of C. -/
instance {F : Face C} : CoeOut (Face (F : PointedCone R M)) (Face C) := ⟨Face.embed⟩

lemma Face.embed_restrict (F₁ F₂ : Face C) : embed (F₁.restrict F₂) = F₁ ⊓ F₂ := rfl

lemma Face.embed_restrict_of_le {F₁ F₂ : Face C} (hF : F₂ ≤ F₁) :
    embed (F₁.restrict F₂) = F₂ := by simp [embed_restrict, hF]

lemma Face.restrict_embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) :
    F₁.restrict (embed F₂) = F₂ := by
  unfold restrict embed; congr
  simpa using F₂.isFaceOf.le_self

lemma Face.embed_le {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : F₂ ≤ F₁ := by
  rw [← restrict_embed F₂, embed_restrict]
  simp only [inf_le_left]

/-- The isomorphism between a face's face lattice and the interval in the cone's face
 lattice below the face. -/
def Face.orderIso (F : Face C) : Face (F : PointedCone R M) ≃o Set.Icc ⊥ F where
  toFun G := ⟨G, bot_le, Face.embed_le G⟩
  invFun G := F.restrict G
  left_inv := restrict_embed
  right_inv G := by simp only [embed_restrict_of_le G.2.2]
  map_rel_iff' := @fun _ _ => by simp [embed]

-- can we get this for free from `Face.orderIso`?
def Face.orderEmbed (F : Face C) : Face (F : PointedCone R M) ↪o Face C := sorry


-- ## EMBED II

lemma IsFaceOf.cone_restrict (S : Submodule R M) {C F : PointedCone R M} (h : F.IsFaceOf C) :
    (F.restrict S).IsFaceOf (C.restrict S) := by sorry

-- lemma isFaceOf_cone_embed_iff'' {S : Submodule R M} {C : PointedCone R M} {F : PointedCone R S} :
--     (F.embed).IsFaceOf C ↔ F.IsFaceOf (C.restrict S) := by sorry

def Face.cone_restrict (S : Submodule R M) {C : PointedCone R M} (F : Face C) :
    Face (C.restrict S) := ⟨_, F.isFaceOf.cone_restrict S⟩

-- def Face.cone_embed'' {S : Submodule R M} {C : PointedCone R M} (F : Face (C.restrict S)) :
--     Face (C) := ⟨_, isFaceOf_cone_embed_iff''.mpr F.isFaceOf⟩

-- lemma IsFaceOf.cone_embed {S : Submodule R M} {C F : PointedCone R S} (h : F.IsFaceOf C) :
--     (F.embed).IsFaceOf C.embed := by sorry

@[simp] lemma isFaceOf_cone_embed_iff {S : Submodule R M} {C F : PointedCone R S} :
    (F.embed).IsFaceOf C.embed ↔ F.IsFaceOf C := by sorry

lemma isFaceOf_of_cone_embed_iff {S : Submodule R M} {C : PointedCone R S} {F : PointedCone R M} :
    (F.restrict S).IsFaceOf C ↔ F.IsFaceOf (C.embed) := by sorry

def Face.cone_embed {S : Submodule R M} {C : PointedCone R S} (F : Face C) :
    Face (C.embed) := ⟨_, isFaceOf_cone_embed_iff.mpr F.isFaceOf⟩

def Face.of_cone_embed {S : Submodule R M} {C : PointedCone R S} (F : Face C.embed) :
    Face (C) := ⟨_, isFaceOf_of_cone_embed_iff.mpr F.isFaceOf⟩

instance {S : Submodule R M} {C : PointedCone R S} : Coe (Face C) (Face C.embed) where
  coe F := F.cone_embed

instance {S : Submodule R M} {C : PointedCone R S} : Coe (Face C.embed) (Face C) where
  coe F := F.of_cone_embed

def embed_face_orderIso {S : Submodule R M} (C : PointedCone R S) : Face C ≃o Face C.embed where
  toFun := .cone_embed
  invFun := .of_cone_embed
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry


-- ## MAP

-- analogous lemmas for comap

lemma isFaceOf_map_iff_of_injOn {f : M →ₗ[R] N} (hf : ker f ⊓ (Submodule.span R C) = ⊥) :
    (PointedCone.map f F).IsFaceOf (.map f C) ↔ F.IsFaceOf C := by
  sorry

lemma isFaceOf_map_iff {f : M →ₗ[R] N} (hf : Injective f) :
    (PointedCone.map f F).IsFaceOf (.map f C) ↔ F.IsFaceOf C := by
  simp only [isFaceOf_def_iff, mem_map, gt_iff_lt, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at *
  simp only [← map_add, ← map_smul, hf.eq_iff, exists_eq_right]
  constructor
  · intro hF x hx y hy c hc hxy
    exact hF x hx y hy c hc _ hxy rfl
  · intro hF x hx y hy c hc z hz rfl
    exact hF x hx y hy c hc hz

lemma IsFaceOf.map {f : M →ₗ[R] N} (hf : Injective f) (hF : F.IsFaceOf C) :
    (map f F).IsFaceOf (map f C) := (isFaceOf_map_iff hf).mpr hF

lemma IsFaceOf.map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
    (PointedCone.map (e : M →ₗ[R] N) F).IsFaceOf (.map e C) := hF.map e.injective

def Face.map {f : M →ₗ[R] N} (hf : Injective f) (F : Face C) : Face (map f C)
    := ⟨_, F.isFaceOf.map hf⟩

def Face.map_equiv (e : M ≃ₗ[R] N) (F : Face C) : Face (PointedCone.map (e : M →ₗ[R] N) C)
    := F.map e.injective

lemma Face.map_inj (f : M →ₗ[R] N) (hf : Injective f) :
    Injective (map hf : Face C → Face _) := sorry

def map_face (C : PointedCone R M) {f : M →ₗ[R] N} (hf : Injective f) :
    Face (map f C) ≃o Face C where
  toFun := sorry
  invFun := Face.map hf
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry

def map_face_equiv (C : PointedCone R M) (e : M ≃ₗ[R] N) :
    Face (map (e : M →ₗ[R] N) C) ≃o Face C := C.map_face e.injective


-- ## QUOT / FIBER

abbrev Face.quotMap (F : Face C) := mkQ F.span

-- def quotBy (C : PointedCone R M) (F : Face C) : PointedCone R (M ⧸ F.span) := map F.quotMap C

/-- The cone obtained by quotiening by the face's linear span. -/
abbrev Face.quot (F : Face C) : PointedCone R (M ⧸ F.span) := .map F.quotMap C

def Face.quotFace (F G : Face C) : Face (F.quot) :=
    ⟨F.quot ⊓ PointedCone.map F.quotMap G, by sorry⟩

def Face.fiberFace {F : Face C} (G : Face (F.quot)) : Face C :=
    ⟨C ⊓ PointedCone.comap F.quotMap G, by sorry⟩

/-- Faces of a quotient cone can naturally be considered as faces of the cone. -/
instance {F : Face C} : CoeOut (Face F.quot) (Face C) := ⟨Face.fiberFace⟩

lemma Face.fiber_quot (F G : Face C) : fiberFace (F.quotFace G) = F ⊔ G := sorry

lemma Face.fiber_quot_of_le {F G : Face C} (h : F ≤ G) : fiberFace (F.quotFace G) = G :=
     by simp [fiber_quot, h]

lemma Face.quot_fiber {F : Face C} (G : Face (F.quot)) : F.quotFace (fiberFace G) = G := sorry

lemma Face.le_fiber {F : Face C} (G : Face (F.quot)) : F ≤ fiberFace G := sorry

/-- The isomorphism between a quotient's face lattice and the interval in the cone's face
 lattice above the face. -/
def Face.quot_orderIso (F : Face C) : Face F.quot ≃o Set.Icc F ⊤ where
  toFun G := ⟨G, le_fiber G, le_top⟩
  invFun G := F.quotFace G
  left_inv := quot_fiber
  right_inv G := by simp only [fiber_quot_of_le G.2.1]
  map_rel_iff' := by intro G G'; simp; sorry

def Face.quot_orderEmbed (F : Face C) : Face F.quot ↪o Face C := sorry


-- ## PROD

lemma isFaceOf_prod {C₁ C₂ F₁ F₂ : PointedCone R M} :
    F₁.IsFaceOf C₁ ∧ F₂.IsFaceOf C₂ ↔ IsFaceOf (F₁.prod F₂) (C₁.prod C₂) := sorry

def Face.prod {C₁ C₂ : PointedCone R M} (F₁ : Face C₁) (F₂ : Face C₂) : Face (C₁.prod C₂) :=
  ⟨_, isFaceOf_prod.mp ⟨F₁.isFaceOf, F₂.isFaceOf⟩⟩

def Face.prod_left {C₁ C₂ : PointedCone R M} (F : Face (C₁.prod C₂)) : Face C₁ := sorry

def Face.prod_right {C₁ C₂ : PointedCone R M} (F : Face (C₁.prod C₂)) : Face C₂ := sorry

lemma Face.prod_prod_left {C₁ C₂ : PointedCone R M} (F₁ : Face C₁) (F₂ : Face C₂) :
    (F₁.prod F₂).prod_left = F₁ := sorry

lemma Face.prod_prod_right {C₁ C₂ : PointedCone R M} (F₁ : Face C₁) (F₂ : Face C₂) :
    (F₁.prod F₂).prod_right = F₂ := sorry

def prod_face_orderIso (C : PointedCone R M) (D : PointedCone R N) :
    Face (C.prod D) ≃o Face C × Face D := sorry


-- ## SUP

def indep (C D : PointedCone R M) :=
    Disjoint (Submodule.span R C) (Submodule.span R (D : Set M))

-- NOTE: might already exist for submodules
def exists_map_prod_sup (C D : PointedCone R M) (h : C.indep D) :
    ∃ e : M × M →ₗ[R] M, Injective e ∧ map e (C.prod D) = C ⊔ D := sorry

def sup_face_orderIso (C D : PointedCone R M) (h : C.indep D) :
    Face (C ⊔ D) ≃o Face C × Face D := sorry

def proper (C : PointedCone R M) :
    PointedCone R (Submodule.span R (C : Set M)) := restrict (Submodule.span (M := M) R C) C

-- def exists_map_prod_sup' (C D : PointedCone R M) (h : C.indep D) :
--     ∃ e : M × M ≃ₗ[R] M, map e (C.prod D) = C ⊔ D := sorry


-- ## INF

lemma IsFaceOf.inf_cone (h : F₁.IsFaceOf C₁) (C₂ : PointedCone R M) :
    (F₁ ⊓ C₂).IsFaceOf (C₁ ⊓ C₂) := by sorry

def Face.inf_cone (F₁ : Face C₁) (C₂ : PointedCone R M) : Face (C₁ ⊓ C₂)
    := ⟨_, F₁.isFaceOf.inf_cone C₂⟩

def Face.inf_cone_orderHom (C₂ : PointedCone R M) : Face C₁ →o Face (C₁ ⊓ C₂) where
  toFun F := F.inf_cone C₂
  monotone' := sorry

lemma IsFaceOf.inf_face (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by sorry

def Face.inf_face (F₁ : Face C₁) (F₂ : Face C₂) : Face (C₁ ⊓ C₂)
    := ⟨_, F₁.isFaceOf.inf_face F₂.isFaceOf⟩

def Face.inf_face_orderHom (F₂ : Face C₂) : Face C₁ →o Face (C₁ ⊓ C₂) where
  toFun F := F.inf_face F₂
  monotone' := sorry

def Face.inf_face_orderHom2 : Face C₁ × Face C₂ →o Face (C₁ ⊓ C₂) where
  toFun F := F.1.inf_face F.2
  monotone' := sorry

-- def Face.inf2_left (F : Face (C₁ ⊓ C₂)) : Face C₁ := sorry -- sInf {F' : Face C₁ | F' ⊓ C₂ = F }

-- def Face.inf2_right (F : Face (C₁ ⊓ C₂)) : Face C₂ := sorry

-- lemma Face.inf2_left_right (F : Face (C₁ ⊓ C₂)) :
--     inf2 F.inf2_left F.inf2_right = F := sorry


end PointedCone




namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}
variable (hC : C.IsDualClosed p)

def faceSet : Set (Face C) := ⊤

variable [Fact p.IsFaithfulPair] in
lemma IsFaceOf.isDualClosed_of_isDualClosed (hF : F.IsFaceOf C) :
    F.IsDualClosed p := by sorry

theorem auxLemma (hC : C.IsDualClosed p) (h : Finite (Face C)) (hlin : C.Salient) :
    C.FG := by sorry

-- ## RELINT

/- A non-topological variant of the relative interior.
  Below two definitions are given. If they are not equivalent, then the more general one should
  be chose and equivalence should be proven when it holds.
-/

def relint (C : PointedCone R M) : ConvexCone R M where
  carrier := {x ∈ C | ∀ F : Face C, x ∈ F → F = C}
  smul_mem' c hc x hx := by
    constructor
    · sorry
    · sorry
  add_mem' x hx y hy := by
    simp
    constructor
    · sorry
    · sorry

theorem relint_def_sInf (C : PointedCone R M) :
    C.relint = sInf {s | dual p.flip (dual p s) = C} := sorry

def min_face {x : M} (h : x ∈ C) : Face C := sorry -- sInf {F : Face C | x ∈ F}

theorem relint_def_min (C : PointedCone R M) :
    C.relint = { x ∈ C | C.min_face (x := x) sorry = C } := sorry

/-- The relative interior is non-empty. -/
lemma relint_nonempty (C : PointedCone R M) : C.relint ≠ ⊥ := sorry

/-- The relative interior is non-empty. -/
lemma relint_nonempty' (C : PointedCone R M) : Nonempty C.relint := sorry

lemma relint_disj (F₁ F₂ : Face C) :
    F₁ ≠ F₂ ↔ Disjoint (relint F₁) (relint F₂) (α := ConvexCone R M) := sorry

lemma relint_cover (C : PointedCone R M) :
    ⋃₀ ((SetLike.coe ∘ relint ∘ Face.toPointedCone) '' C.faceSet) = C := sorry

def relint_partition (C : PointedCone R M) : Partition (C : Set M) where
  parts := { relint (F : PointedCone R M) | (F : Face C) }
  sSupIndep' := sorry
  bot_notMem' := by
    simp only [Set.bot_eq_empty, Set.mem_setOf_eq, ConvexCone.coe_eq_empty, not_exists]
    exact fun F => relint_nonempty (F : PointedCone R M)
  sSup_eq' := by
    ext x
    -- simp; exact relint_partition C
    sorry

-- ## EXPOSED

def HalfspaceOrTop.IsSupportAt (H : HalfspaceOrTop R M) (F : Face C) :=
    C ≤ H ∧ C ⊓ H.boundary = F

def HyperplaneOrTop.IsSupportAt (H : HyperplaneOrTop R M) (F : Face C) :=
    ∃ H' : HalfspaceOrTop R M, H'.boundary = H ∧ C ≤ H' ∧ C ⊓ H = F

def Face.IsExposed (F : Face C) := ∃ H : HalfspaceOrTop R M, H.IsSupportAt F
-- def Face.IsExposed (F : Face C) := ∃ H : HalfspaceOrTop R M, C ≤ H ∧ C ⊓ H.boundary = F

lemma Face.isExpose_def (F : Face C) :
    F.IsExposed ↔ ∃ φ : M →ₗ[R] R, (∀ x ∈ C, φ x ≥ 0) ∧ (∀ x ∈ C, φ x = 0 ↔ x ∈ F) := sorry

theorem bot_isExposed (hC : C.IsDualClosed p) : (⊥ : Face C).IsExposed := by
  -- reduce to salient case via quotients
  wlog h : C.Salient
  · sorry
  rw [Face.isExpose_def]
  have hC : C.IsDualClosed (Dual.eval R M) := hC.to_eval
  obtain ⟨D, hD, hDC⟩ := hC.exists_of_dual_flip
  let φ := D.relint_nonempty'.some
  use φ
  constructor
  · sorry
  · sorry

theorem IsExposed.of_isExposed_face_quot {F : Face C} {G : Face (F.quot)} (hG : G.IsExposed) :
    F.IsExposed := by
  -- idea: the comap of a supporting halfspace is again a supporting halfspace.
  sorry

theorem IsDualClosed.quot (hC : C.IsDualClosed p) (F : Face C) :
    F.quot.IsDualClosed (Dual.eval R (M ⧸ F.span)) := sorry

end PointedCone



namespace Submodule

variable {R : Type*} [Semiring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

lemma face_eq_top {S : Submodule R M} {F : PointedCone R M} (hF : F.IsFaceOf S) :
    F = S := by sorry

lemma Face.eq_top {S : Submodule R M} (F : Face (S : PointedCone R M)) :
    F = ⊤ := by sorry

instance face_unique {S : Submodule R M} : Unique (Face (S : PointedCone R M)) where
  default := ⊤
  uniq F := Submodule.Face.eq_top F

example {S : Submodule R M} : Finite (Face (S : PointedCone R M)) := inferInstance

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C : PointedCone R M}

lemma face_bot_eq_top {S : Submodule R M} : (⊥ : Face (S : PointedCone R M)) = ⊤ := by sorry

end Submodule
