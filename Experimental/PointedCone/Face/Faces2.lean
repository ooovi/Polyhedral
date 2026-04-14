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

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Finite.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Dual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Halfspace

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
 * exposed
   * bot and top are exposed
   * if there are finitely many, then all faces are exposed
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
variable {S : Submodule R M}
variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}

-- ## MISC

lemma IsFaceOf.def''' (hF : F.IsFaceOf C) : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ F → x ∈ F :=
  sorry

lemma IsFaceOf.def'' (hF : F.IsFaceOf C) {s : Finset M} (hs : ∀ S ∈ s, S ∈ C)
    (hsum : ∑ S ∈ s, S ∈ F) : ∀ S ∈ s, S ∈ F := sorry

lemma IsFaceOf.inf' (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C := sorry

abbrev Face.Proper (F : Face C) := F ≠ ⊤

abbrev Face.Trivial (F : Face C) := F = ⊥ ∨ F = ⊤
abbrev Face.Nontrivial (F : Face C) := ⊥ < F ∧ F < ⊤

/-- The linear span of the face. -/
-- abbrev Face.span (F : Face C) : Submodule R M := Submodule.span R F

-- lemma IsFaceOf.iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
--     F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂ := by
--   constructor
--   · exact le_self
--   rw [IsFaceOf.iff_mem_of_mul_add_mem] at ⊢ h₁
--   exact fun h => ⟨h, fun x hx y hy => h₁.2 x (h₂.le_self hx) y (h₂.le_self hy)⟩

lemma IsFaceOf.of_cone_iff_of_face (h₁ : F₁.IsFaceOf C) (h₂ : F₂ ≤ F₂) :
    F₂.IsFaceOf C ↔ F₂.IsFaceOf F₁ := sorry


-- ## RESTRICT / EMBED

-- TODO: move to Faces lean file

lemma IsFaceOf.restrict (S : Submodule R M) (hF : F.IsFaceOf C) :
    (restrict S F).IsFaceOf (restrict S C) := ⟨restrict_mono S hF.1, hF.2⟩ -- hF.comap S.subtype

lemma IsFaceOf.embed {S : Submodule R M} {C F : PointedCone R S} (hF : F.IsFaceOf C) :
    (embed F).IsFaceOf (embed C) := hF.map S.subtype_injective

----

lemma IsFaceOf.restrict' (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    (F₁ ⊓ F₂).IsFaceOf F₁ := (h₁.of_cone_iff_of_face (le_refl _)).mp (h₁.inf' h₂)

-- Change order of arguments in `IsFaceOf.trans` because currently inconsistent with `embed`?
alias IsFaceOf.embed' := IsFaceOf.trans

-- def Face.restrict (F₁ F₂ : Face C) : Face (F₁ : PointedCone R M) :=
--     ⟨F₁ ⊓ F₂, F₁.isFaceOf.restrict F₂.isFaceOf⟩

-- def Face.embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : Face C :=
--     ⟨F₂, F₂.isFaceOf.trans F₁.isFaceOf⟩

-- /-- A face of a face of C coerces to a face of C. -/
-- instance {F : Face C} : CoeOut (Face (F : PointedCone R M)) (Face C) := ⟨Face.embed⟩

-- lemma Face.embed_restrict (F₁ F₂ : Face C) : embed (F₁.restrict F₂) = F₁ ⊓ F₂ := rfl

-- lemma Face.embed_restrict_of_le {F₁ F₂ : Face C} (hF : F₂ ≤ F₁) :
--     embed (F₁.restrict F₂) = F₂ := by simp [embed_restrict, hF]

-- lemma Face.restrict_embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) :
--     F₁.restrict (embed F₂) = F₂ := by
--   unfold restrict embed; congr
--   simpa using F₂.isFaceOf.le_self

-- lemma Face.embed_le {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : F₂ ≤ F₁ := by
--   rw [← restrict_embed F₂, embed_restrict]
--   simp only [inf_le_left]


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


-- ## LINEAL

lemma Face.lineal_eq (F : Face C) : PointedCone.lineal F = C.lineal := sorry


-- ## MAP

-- analogous lemmas for comap

lemma isFaceOf_map_iff_of_injOn {f : M →ₗ[R] N} (hf : ker f ⊓ (Submodule.span R C) = ⊥) :
    (PointedCone.map f F).IsFaceOf (.map f C) ↔ F.IsFaceOf C := by
  sorry

-- lemma IsFaceOf.map {f : M →ₗ[R] N} (hf : Injective f) (hF : F.IsFaceOf C) :
--     (map f F).IsFaceOf (map f C) := (isFaceOf_map_iff hf).mpr hF

-- lemma IsFaceOf.map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
--     (PointedCone.map (e : M →ₗ[R] N) F).IsFaceOf (.map e C) := hF.map e.injective

-- def Face.map {f : M →ₗ[R] N} (hf : Injective f) (F : Face C) : Face (map f C)
--     := ⟨_, F.isFaceOf.map hf⟩

-- def Face.map_equiv (e : M ≃ₗ[R] N) (F : Face C) : Face (PointedCone.map (e : M →ₗ[R] N) C)
--     := F.map e.injective

-- lemma Face.map_inj (f : M →ₗ[R] N) (hf : Injective f) :
--     Injective (map hf : Face C → Face _) := sorry

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

-- abbrev IsFaceOf.quot {C F : PointedCone R M} (hF : F.IsFaceOf C) := C.quot (Submodule.span R F)

lemma IsFaceOf.quot {C F₁ F₂ : PointedCone R M} (hF₁ : F₁.IsFaceOf C) (hF₂ : F₂.IsFaceOf C)
    (hF : F₂ ≤ F₁) : (F₁.quot F₂.linSpan).IsFaceOf (C.quot F₂.linSpan) := by
  sorry

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

lemma fooo (S : Submodule R M) (hF : F.IsFaceOf (C ⊔ S)) : (F ⊓ C.linSpan).IsFaceOf C := sorry

lemma fooo' (S : Submodule R M) (hF : F.IsFaceOf (C ⊔ S)) : (F ⊓ C.linSpan) ⊔ S = F := sorry

lemma isAtom_iff_span_singleton (C : PointedCone R M) : IsAtom C ↔ ∃ x ≠ 0, span R {x} = C := by
  constructor <;> intro H
  · sorry
  · obtain ⟨x, hx, rfl⟩ := H
    unfold IsAtom
    constructor
    · simp [hx]
    · intro D hD
      ext y
      simp
      constructor <;> intro hy
      · have hD' := (le_of_lt hD) hy
        simp [mem_span_singleton] at hD'
        sorry
      · sorry

lemma IsFaceOf.def' : F.IsFaceOf C ↔
    F ≤ C ∧ ∀ a ≤ C, ∀ b ≤ C, IsAtom a → IsAtom b → (a ⊔ b) ⊓ F ≠ ⊥ → a ≤ F := by
  constructor <;> intro H <;> constructor
  · exact H.1
  · sorry
  · exact H.1
  · intro x y c hx hy hc h
    have H' := H.2 (span R {x}) (by simp [hx]) (span R {y}) (by simp [hy])
    -- have : span R {x} ⊔ span R {y} ≤ F := by
    --   intro z hz
    --   simp [mem_sup] at hz
    --   obtain ⟨x', hx', y', hy', rfl⟩ := hz
    --   rw [mem_span_singleton] at hx' hy'
    --   obtain ⟨c', hc'⟩ := hx'
    --   obtain ⟨d', hd'⟩ := hy'
    --   -- have H := H.2 (span R {x}) (by simp [hx]) (span R {y}) (by simp [hy])
    --   sorry
    have : c • x + y ∈ span R {x} ⊔ span R {y} := by
      simp [mem_sup]
      use c • x
      constructor
      · sorry
      use y
      constructor
      · sorry
      rfl

    sorry

/- Likely theory already exists here: cones >= S and cones in M⧸S are known to be orderIso. -/
#check Submodule.quot_orderIso_Ici_restrictScalars

def Face.sup_orderIso_quot (S : Submodule R M) : Face (C ⊔ S) ≃o Face (C.quot S) where
  toFun F := ⟨PointedCone.map S.mkQ F.1, by
    --rw [IsFaceOf.def]
    constructor
    · simp [F.isFaceOf.le]
    · intro x y c hx hy hc H
      -- let f := surjInv S.mkQ_surjective
      -- let x' := f x
      -- let y' := f y
      simp only [mem_map] at hx hy
      obtain ⟨x', hx, rfl⟩ := hx
      obtain ⟨y', hy, rfl⟩ := hy
      have h : C ≤ C ⊔ S := le_sup_left
      have hx : x' ∈ C ⊔ S := h hx
      have hy : y' ∈ C ⊔ S := h hy
      have hF := F.isFaceOf.mem_of_smul_add_mem hx hy hc
      repeat rw [← map_smul] at H
      rw [← map_add] at H
      rw [mem_map] at H
      obtain ⟨z, hzF, hz⟩ := H
      simp only [mem_map]
      sorry ⟩
  invFun F := ⟨PointedCone.comap S.mkQ F.1, by
    sorry⟩
  left_inv F := by
    simp
    congr
    sorry
  right_inv F := by
    simp
    congr
    sorry
  map_rel_iff' := by
    intro F G
    simp only [Equiv.coe_fn_mk, toPointedCone, map_mkQ_le_iff_sup_le]
    constructor <;> intro h
    · simp only [sup_le_iff, le_sup_right, and_true] at h
      have : G.1 ⊔ S ≤ G.1 := by
        sorry
      sorry -- # broken by PR
      --exact le_trans h this
    · sorry -- # broken by PR
      -- exact sup_le_sup_right h S

def Face.sup_orderIso (F : Face C) : Face (C ⊔ linSpan F.1) ≃o Set.Icc F ⊤ where
  toFun G := ⟨⟨G ⊓ C, sorry⟩, sorry⟩
  invFun G := ⟨G ⊔ linSpan F.1, sorry⟩
  left_inv G := by
    simp
    congr
    sorry
  right_inv G := by
    simp
    congr
    sorry
  map_rel_iff' := by
    intro G H
    simp
    sorry


-- ## PROD

lemma isFaceOf_prod {C₁ C₂ F₁ F₂ : PointedCone R M} :
    F₁.IsFaceOf C₁ ∧ F₂.IsFaceOf C₂ ↔ IsFaceOf (F₁.prod F₂) (C₁.prod C₂) := sorry

-- def Face.prod {C₁ C₂ : PointedCone R M} (F₁ : Face C₁) (F₂ : Face C₂) : Face (C₁.prod C₂) :=
--   ⟨_, isFaceOf_prod.mp ⟨F₁.isFaceOf, F₂.isFaceOf⟩⟩

-- def Face.prod_left {C₁ C₂ : PointedCone R M} (F : Face (C₁.prod C₂)) : Face C₁ := sorry

-- def Face.prod_right {C₁ C₂ : PointedCone R M} (F : Face (C₁.prod C₂)) : Face C₂ := sorry

-- lemma Face.prod_prod_left {C₁ C₂ : PointedCone R M} (F₁ : Face C₁) (F₂ : Face C₂) :
--     (F₁.prod F₂).prod_left = F₁ := sorry

-- lemma Face.prod_prod_right {C₁ C₂ : PointedCone R M} (F₁ : Face C₁) (F₂ : Face C₂) :
--     (F₁.prod F₂).prod_right = F₂ := sorry

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


-- ## COMB EQUIV

def Face.restrict (S : Submodule R M) (F : Face C) : Face (C.restrict S) :=
  ⟨_, F.isFaceOf.restrict S⟩

-- @[simp]
lemma Face.restrict_def (S : Submodule R M) (F : Face C) :
    F.restrict S = PointedCone.restrict S F := rfl

@[coe] def Face.embed {S : Submodule R M} {C : PointedCone R S} (F : Face C) : Face (C.embed) :=
  ⟨_, F.isFaceOf.embed⟩

@[simp] lemma Face.embed_def (S : Submodule R M) {C : PointedCone R S} (F : Face C) :
    F.embed = PointedCone.embed F.1 := rfl

@[simp] lemma Face.coe_embed (S : Submodule R M) {C : PointedCone R S} (F : Face C) :
    (F.embed : PointedCone R M) = PointedCone.embed (F : PointedCone R S) := rfl

/-- Two cones are combinatorially equivalent if their face posets are order isomorphic. -/
abbrev CombEquiv (C D : PointedCone R M) := Nonempty (Face C ≃o Face D)

/-- Denotes combinatorial equivalence of pointed cones. Notation for `CombEquiv`. -/
infixl:100 " ≃c " => CombEquiv

def embed_combEquiv (C : PointedCone R S) : Face (embed C) ≃o Face C where
  toFun F := ⟨PointedCone.restrict S F, sorry⟩ -- F.isFaceOf.restrict S⟩
  invFun := .embed
  left_inv F := by simp [Face.embed, embed_restrict, le_trans F.isFaceOf.le embed_le]
  right_inv F := by simp [Face.embed]; sorry
  map_rel_iff' := by
    intro F G
    simp
    constructor <;> intro h
    · sorry
    · exact restrict_mono S h

-- def restrict_combEquiv_of_codisjoint_lineal' (hCS : Codisjoint S C.lineal) :
--     Face (restrict S C) ≃o Face C := by
--   let e := embed_combEquiv (restrict S C)
--   rw [embed_restrict] at e
--   -- seems to require Face (C ⊓ S) ≃o Face C
--   sorry

def restrict_combEquiv_of_codisjoint_lineal (hCS : Codisjoint S C.lineal) :
    Face (restrict S C) ≃o Face C where
  toFun F := ⟨embed F.1 ⊔ C.lineal, by
    have h : C = C ⊔ C := by simp only [le_refl, sup_of_le_left]
    nth_rw 3 [h]
    sorry⟩
  invFun := Face.restrict S
  left_inv F := by
    simp [Face.restrict, ← Face.toPointedCone_eq_iff]
    apply embed_injective
    simp
    sorry
    -- rw [inf_comm]
    -- rw [← sup_inf_assoc_of_le_restrictScalars]
    -- · simp only [sup_eq_left]
      -- refine le_trans inf_le_left ?_
      --unfold Face.embed'
      -- sorry
    -- · simp
  right_inv F := by
    simp only [Face.restrict, Face.toPointedCone, embed_restrict, inf_comm,
      ← Face.toPointedCone_eq_iff]
    rw [← inf_sup_assoc_of_submodule_le]
    · simp [← restrictScalars_sup, hCS.eq_top]
    · exact F.isFaceOf.lineal_le
  map_rel_iff' := by
    simp
    intro F G
    constructor <;> intro h
    · sorry
    · sorry

-- def embed_combEquiv' (C : PointedCone R S) : Face (embed C) ≃o Face C := by
--   let e := restrict_combEquiv_of_codisjoint_lineal (S := S) (C := embed C) ?_
--   · rw [restrict_embed] at e
--     exact e.symm
--   -- seems to not work
--   sorry

def inf_combEquiv_of_codisjoint_lineal' (hSC : Codisjoint S C.lineal) :
    Face (C ⊓ S) ≃o Face C := by
  let er := restrict_combEquiv_of_codisjoint_lineal hSC
  let ee := embed_combEquiv (restrict S C)
  rw [embed_restrict, inf_comm] at ee
  exact ee.trans er

-- We use the term `combEquiv` for `OrderEquiv` if it is between the face posets
/-- The combinatorial equivalence between a pointed cone `C` and the pointed cone `C ⊓ S`, where
  `S` is a submodule complementary to the lineality of `C`. The existence of this isomorphism is
  crucial because it shows that the face structure can be studied on the salient part. In the
  case of polyhedral cones, this yields a reduction to FG cones. -/
def inf_combEquiv_of_isCompl_lineal (hS : IsCompl S C.lineal) :
    Face (C ⊓ S) ≃o Face C where
  toFun F := ⟨F ⊔ C.lineal, by -- TODO: this construction should exist on the level of `Face`.
    sorry -- # broken since PR
    -- have h := F.isFaceOf.sup (.refl C.lineal) ?_
    -- · rw [← inf_sup_assoc_of_submodule_le] at h
    --   · simpa [← coe_sup, hS.codisjoint.eq_top] using h
    --   · exact lineal_le C
    -- · rw [ofSubmodule_linSpan]
    --   refine Disjoint.mono_left ?_ hS.disjoint
    --   nth_rw 2 [← span_eq S]
    --   exact span_monotone (by simp)
    ⟩
  invFun F := ⟨F ⊓ S, F.isFaceOf.inf sorry⟩ -- # broken since PR
    -- TODO: this construction should already exist on the level of `Face`.
  left_inv F := by
    simp only [Face.toPointedCone]; congr
    rw [← sup_inf_assoc_of_le_submodule]
    · simp [← coe_inf, inf_comm, hS.disjoint.eq_bot]
    · exact le_trans F.isFaceOf.le inf_le_right
  right_inv F := by
    simp only [Face.toPointedCone]; congr
    rw [← inf_sup_assoc_of_submodule_le]
    · simp [← coe_sup, hS.codisjoint.eq_top]
    · exact F.isFaceOf.lineal_le
  map_rel_iff' := by
    sorry -- # broken since PR
    -- intro F G
    -- simp only [Face.toPointedCone, Equiv.coe_fn_mk, Face.toPointedCone_le_iff, sup_le_iff,
    --   le_sup_right, and_true]
    -- constructor <;> intro h
    -- · have h := inf_le_inf_right (S : PointedCone R M) h
    --   rw [← sup_inf_assoc_of_le_submodule] at h
    --   · have h' := le_trans F.isFaceOf.le inf_le_right
    --     simpa [h', ← coe_inf, inf_comm, hS.disjoint.eq_bot] using h
    --   · exact le_trans G.isFaceOf.le inf_le_right
    -- · exact le_trans h le_sup_left

lemma exists_salient_combEquiv (C : PointedCone R M) :
    ∃ D : PointedCone R M, D.Salient ∧ D ≃c C := by
  obtain ⟨S, hS⟩ := Submodule.exists_isCompl C.lineal
  exact ⟨_, inf_salient hS.disjoint, ⟨inf_combEquiv_of_isCompl_lineal hS.symm⟩⟩

-- lemma mem_span_setminus_iff_span_isFaceOf {C : PointedCone R M} (hC : C.DualClosed p)
--     (x : M) (hx : x ∈ C) :
--     x ∉ span R (C \ span R {x}) ↔ (span R {x}).IsFaceOf C := by classical
--   constructor <;> intro h
--   · have hfar := farkas p (span R (↑C \ ↑(span R {x})))

--     sorry
--   · rw [mem_span_iff_exists_finset_subset]
--     push_neg
--     intro f s hs hfs
--     by_contra H
--     have hx : x ∈ span R {x} := by simp
--     nth_rw 2 [← H] at hx
--     have hss : ∀ x ∈ s, x ∈ C := fun _ hx => (hs hx).1
--     have hfss : ∀ x ∈ s, 0 ≤ f x := by simp
--     have h0 : ∃ x ∈ s, 0 < f x := by
--       by_contra H'
--       push_neg at H'
--       have h0 : ∀ x ∈ s, f x = 0 := by
--         intro x hx
--         exact le_antisymm (H' x hx) (hfss x hx)
--       -- show in H: 0 = x
--       -- leads to contra in hs
--       sorry
--     obtain ⟨y, hy, hy0⟩ := h0
--     have hh := h.mem_of_sum_smul_mem''' hss hfss hx y hy hy0
--     have H := hs hy
--     simp at H
--     exact H.2 hh



end PointedCone




namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}
variable (hC : C.DualClosed p)

def faceSet : Set (Face C) := ⊤

variable [Fact p.IsFaithfulPair] in
lemma IsFaceOf.isDualClosed_of_isDualClosed (hF : F.IsFaceOf C) :
    F.DualClosed p := by sorry

theorem auxLemma (hC : C.DualClosed p) (h : Finite (Face C)) (hlin : C.Salient) :
    C.FG := by sorry

end PointedCone



namespace Submodule

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {S : Submodule R M}
variable {C : PointedCone R M}

lemma IsFaceOf.Submodule.eq_self {F : PointedCone R M} (hF : F.IsFaceOf S) :
    F = S := by
  rw [le_antisymm_iff]
  constructor
  · exact hF.le
  intro x hx
  have hy : -x ∈ S := by simpa using hx
  exact hF.mem_of_add_mem hx hy (by simp)

lemma Face.eq_top (F : Face (S : PointedCone R M)) : F = ⊤ := by
  rw [← Face.toPointedCone_eq_iff]
  simp
  have h := IsFaceOf.Submodule.eq_self F.isFaceOf
  -- rw [h]
  sorry

lemma Face.eq_bot (F : Face (S : PointedCone R M)) : F = ⊥ := by sorry

instance face_unique : Unique (Face (S : PointedCone R M)) where
  default := ⊤
  uniq := Face.eq_top

example : Finite (Face (S : PointedCone R M)) := inferInstance

lemma face_bot_eq_top : (⊥ : Face (S : PointedCone R M)) = ⊤ := by sorry

lemma eq_lineal_of_forall_face_eq_self (h : ∀ F : PointedCone R M, F.IsFaceOf C → F = C) :
    C = C.lineal := by rw [h _ (IsFaceOf.lineal C)]

-- lemma foo (h : Unique (Face C)) : C = C.lineal := by
--   have h' := h.uniq Face.lineal
--   have h'' := h.uniq C
--   sorry

-- lemma foo (h : ∀ F, F.IsFaceOf C → F = C.lineal) : C = C.lineal := by
--   have h' := h.uniq Face.lineal
--   have h'' := h.uniq C
--   sorry

end Submodule
