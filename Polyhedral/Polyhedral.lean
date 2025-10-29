/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Field
import Polyhedral.ExtremeFaces

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

open Function Module OrderDual
open Submodule hiding span dual IsDualClosed
open PointedCone


namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C : PointedCone R M}
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}


-- ## MISC

/-- The linear span of the face. -/
abbrev Face.span (F : Face C) : Submodule R M := Submodule.span R F

lemma IsFaceOf.iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂ := sorry

-- Change order of arguments in `IsFaceOf.trans` because currently inconsistent with `embed`?
alias IsFaceOf.embed := IsFaceOf.trans

lemma IsFaceOf.restrict (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    (F₁ ⊓ F₂).IsFaceOf F₁ := sorry


-- ## DUAL

def Face.dual (F : Face C) : Face (dual p C) := ⟨_, F.isFaceOf.subdual_dual p⟩

lemma Face.dual_antitone : Antitone (dual : Face C → Face (.dual p C)) := by
  sorry


-- ## RESTRICT / EMBED

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
    F₁.restrict (embed F₂) = F₂ := sorry

lemma Face.embed_le {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : F₂ ≤ F₁ := sorry

/-- The isomorphism between a face's face lattice and the interval in the cone's face
 lattice below the face. -/
def Face.orderIso (F : Face C) : Face (F : PointedCone R M) ≃o Set.Icc ⊥ F where
  toFun G := ⟨G, bot_le, Face.embed_le G⟩
  invFun G := F.restrict G
  left_inv := restrict_embed
  right_inv G := by simp only [embed_restrict_of_le G.2.2]
  map_rel_iff' := by intro G G'; simp; sorry -- should be easy, maybe its own lemma?

-- can we get this for free from `Face.orderIso`?
def Face.orderEmbed (F : Face C) : Face (F : PointedCone R M) ↪o Face C := sorry


-- ## MAP

lemma IsFaceOf.map (f : M →ₗ[R] N) (hf : Injective f) (hF : F.IsFaceOf C) :
    (map f F).IsFaceOf (map f C) := sorry

lemma IsFaceOf.map_iff (f : M →ₗ[R] N) (hf : Injective f) :
    (PointedCone.map f F).IsFaceOf (.map f C) ↔ F.IsFaceOf C := sorry

lemma IsFaceOf.map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
    (PointedCone.map (e : M →ₗ[R] N) F).IsFaceOf (.map e C) :=
  hF.map (e : M →ₗ[R] N) e.injective

def Face.map (f : M →ₗ[R] N) (hf : Injective f) (F : Face C) : Face (map f C)
    := ⟨_, F.isFaceOf.map f hf⟩

def Face.map_equiv (e : M ≃ₗ[R] N) (F : Face C) : Face (PointedCone.map (e : M →ₗ[R] N) C)
    := F.map (e : M →ₗ[R] N) e.injective

lemma Face.map_inj (f : M →ₗ[R] N) (hf : Injective f) :
    Injective (map f hf : Face C → Face _) := sorry

def map_face (C : PointedCone R M) (f : M →ₗ[R] N) (hf : Injective f) :
    Face (map f C) ≃o Face C := sorry

def map_face_equiv (C : PointedCone R M) (e : M ≃ₗ[R] N) :
    Face (map (e : M →ₗ[R] N) C) ≃o Face C := C.map_face (e : M →ₗ[R] N) e.injective


-- ## QUOTIENT

def Face.quotMap (F : Face C) := mkQ F.span

-- def quotBy (C : PointedCone R M) (F : Face C) : PointedCone R (M ⧸ F.span) := map F.quotMap C

/-- The cone obtained by quotiening by the face's linear span. -/
def Face.quot (F : Face C) : PointedCone R (M ⧸ F.span) := .map F.quotMap C

def Face.quotFace (F G : Face C) (h : F ≤ G) : Face (F.quot) :=
    ⟨PointedCone.map F.quotMap G, by sorry⟩

/-- The isomorphism between a quotient's face lattice and the interval in the cone's face
 lattice above the face. -/
def Face.quot_orderIso (F : Face C) : Face F.quot ≃o Set.Icc F ⊤ := by sorry

def Face.quot_orderEmbed (F : Face C) : Face F.quot ↪o Face C := by sorry


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

variable [Fact p.IsFaithfulPair] in
lemma IsFaceOf.isDualClosed_of_isDualClosed (hF : F.IsFaceOf C) :
    F.IsDualClosed p := by sorry

theorem auxLemma (C : PointedCone R M) (hC : C.IsDualClosed p)
    (h : Finite (Face C)) (hlin : C.Salient) : C.FG := by sorry

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

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {C : PointedCone R M}

lemma face_bot_eq_top {S : Submodule R M} : (⊥ : Face (S : PointedCone R M)) = ⊤ := by sorry

end Submodule





/- Next goal: **FG cones are polyhedral**
 * FG cones are dual closed (check)
 * Submodule has a single face
 * face lattice of product is product of face lattices
 * → If C ⊓ S = ⊥, then C ⊔ S has the same face lattice as C
 * (M) Every cone C can be written as C = C' + C.lineal, with C pointed and complementary
 * If C is pointy and dual closed, then generated by 1-dim faces.
 * Every face of C is generated by a subset of the generators of C
   *
 * FG have finitely many faces
   * every face of C is generated by a subset of the generators of C
   * only finitly many subsets of the generators of C → only finitely many faces of C
 * dual of a dual closed cone has opposite face lattice
 * face lattice graded (when??)
-/




variable {𝕜 M N : Type*}

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup M] [AddCommGroup M] [Module 𝕜 M]
variable [AddCommGroup N] [AddCommGroup N] [Module 𝕜 N]
-- variable [AddCommGroup N] [AddCommGroup N] [Module 𝕜 N]

-- /-- A cone is polyhedral if it is dual closed and has finitely many faces. -/
-- structure PointedCone.IsPolyhedral (C : PointedCone 𝕜 M) where
--   finite := Finite (Face C)
--   closed := C.IsDualClosed

variable (𝕜 M) in
/-- A polyhedral cone is a dual closed cone with finitely many faces. -/
structure PolyhedralCone extends PointedCone 𝕜 M where
  /-- A polyhedral cone has finitely many faces. -/
  finiteFaces : Finite (Face toSubmodule)
  /-- A polyhedral cone is dual closed. -/
  dualClosed : IsDualClosed (Dual.eval 𝕜 M) toSubmodule

namespace PolyhedralCone

@[coe] abbrev toPointedCone (C : PolyhedralCone 𝕜 M) : PointedCone 𝕜 M := C.toSubmodule

instance : Coe (PolyhedralCone 𝕜 M) (PointedCone 𝕜 M) where
  coe := toPointedCone

lemma toPointedCone_injective :
    Injective (toPointedCone : PolyhedralCone 𝕜 M → PointedCone 𝕜 M) :=
  sorry -- fun ⟨_, _⟩ _ ↦ by congr!

lemma foo (C : PolyhedralCone 𝕜 M) :
  ∃ D : PolyhedralCone 𝕜 M, D.FG ∧ ∃ S : Submodule 𝕜 M, S.IsDualClosed (Dual.eval 𝕜 M) ∧ D ⊔ S = C
  := sorry

variable [Module.Finite 𝕜 M]

instance : SetLike (PolyhedralCone 𝕜 M) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp toPointedCone_injective

@[simp] lemma coe_toPointedCone (C : PolyhedralCone 𝕜 M) : (C.toPointedCone : Set M) = C := rfl

--------------------------

def of_FG {C : PointedCone 𝕜 M} (hC : C.FG) : PolyhedralCone 𝕜 M
    := ⟨C, Face.finite_of_fg hC, FG.isDualClosed (Dual.eval 𝕜 M) hC⟩

def span (s : Finset M) : PolyhedralCone 𝕜 M := of_FG (Submodule.fg_span <| s.finite_toSet)

def span_of_finite {S : Set M} (hfin : S.Finite) : PolyhedralCone 𝕜 M
  := of_FG (Submodule.fg_span hfin)

instance {C : PolyhedralCone 𝕜 M} :
    CoeOut (PointedCone.Face (C : PointedCone 𝕜 M)) (PolyhedralCone 𝕜 M) := sorry

instance : Coe (Submodule 𝕜 M) (PolyhedralCone 𝕜 M) := sorry

instance : Bot (PolyhedralCone 𝕜 M) := ⟨of_FG fg_bot⟩
instance : Top (PolyhedralCone 𝕜 M) := ⟨of_FG Module.Finite.fg_top⟩

instance : OrderBot (PolyhedralCone 𝕜 M) := ⟨sorry⟩
instance : OrderTop (PolyhedralCone 𝕜 M) := ⟨sorry⟩

instance : Min (PolyhedralCone 𝕜 M) where
  min C D := sorry -- of_FG <| PointedCone.inf_fg C.isFG D.isFG
instance : Max (PolyhedralCone 𝕜 M) where
  max C D := sorry -- of_FG <| PointedCone.sup_fg C.isFG D.isFG
-- NOTE: on cones, ⊔ also acts as Minkowski sum

variable {𝕜 M N : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup M] [Module 𝕜 M]
variable [AddCommGroup N] [Module 𝕜 N]
variable {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜}

theorem isDualClosed_iff_isDualClosed_lineal (P : PolyhedralCone 𝕜 M) :
  IsDualClosed p P ↔ Submodule.IsDualClosed p (lineal P) := by sorry



def of_CoFG {C : PointedCone 𝕜 N} (hC : C.CoFG p) : PolyhedralCone 𝕜 N
    := ⟨C, by sorry, by sorry⟩

variable (p) in
def dual (C : PolyhedralCone 𝕜 M) : PolyhedralCone 𝕜 N
  := sorry -- of_FG (PointedCone.dual_fg p C.isFG)

def dual_of_fg (C : PointedCone 𝕜 M) (hC : C.FG) : PolyhedralCone 𝕜 N
  := sorry -- dual p (of_FG hC)

def dual_of_finset (s : Finset M) : PolyhedralCone 𝕜 N
  := sorry -- dual p (of_FG <| Submodule.fg_span s.finite_toSet)

def dual_of_finite (S : Set M) (hS : S.Finite) : PolyhedralCone 𝕜 N
  := sorry -- dual p (of_FG <| Submodule.fg_span hS)

variable [Module.Finite 𝕜 N]
variable {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜} [p.IsPerfPair]

-- probably needs assumptions, such as perfect pairing maybe?
lemma dual_dual_flip (C : PolyhedralCone 𝕜 N) : dual p (dual p.flip C) = C := by
  sorry
lemma dual_flip_dual (C : PolyhedralCone 𝕜 M) : dual p.flip (dual p C) = C := by
  sorry

section Map

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M N M' N' : Type*}
  [AddCommMonoid M] [Module 𝕜 M]
  -- [AddCommGroup N] [Module 𝕜 N]
  [AddCommMonoid M'] [Module 𝕜 M'] [Module.Finite 𝕜 M']
  -- [AddCommGroup N'] [Module 𝕜 N'] [Module.Finite 𝕜 N']

variable (f : M →ₗ[𝕜] M')

theorem _root_.Submodule.FG.comap {S : Submodule 𝕜 M'} (hs : S.FG) : (S.comap f).FG := by
  sorry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {M N M' N' : Type*}
  [AddCommGroup M] [Module 𝕜 M]
  -- [AddCommGroup N] [Module 𝕜 N]
  [AddCommGroup M'] [Module 𝕜 M'] [Module.Finite 𝕜 M']
  -- [AddCommGroup N'] [Module 𝕜 N'] [Module.Finite 𝕜 N']

variable (f : M →ₗ[𝕜] M')

def map (C : PolyhedralCone 𝕜 M) : PolyhedralCone 𝕜 M'
  := of_FG <| Submodule.FG.map (f.restrictScalars _) C.isFG

local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

def comap (C : PolyhedralCone 𝕜 M') : PolyhedralCone 𝕜 M
  := of_FG <| Submodule.FG.comap (f.restrictScalars _) C.isFG

variable [Module.Finite 𝕜 M]

lemma map_dual (C : PolyhedralCone 𝕜 M) :
    dual (Dual.eval 𝕜 M') (map f C) = comap f.dualMap (dual (Dual.eval 𝕜 M) C) := by
  sorry -- ext x; simp

instance : Neg (PolyhedralCone 𝕜 M) where
  neg C := of_FG <| Submodule.FG.map (-.id) C.isFG

instance : Coe (Submodule 𝕜 M) (PolyhedralCone 𝕜 M) where
  coe S := of_FG <| PointedCone.ofSubmodule_fg_of_fg
    <| (Submodule.fg_iff_finiteDimensional S).mpr inferInstance


-- /-- A linear subspace is a polyhedral cone -/
-- lemma IsPolyhedral.submodule (S : Submodule 𝕜 M) : (S : PointedCone 𝕜 M).FG
--   := PointedCone.ofSubmodule.FG_of_FG
--     <| (Submodule.fg_iff_finiteDimensional S).mpr inferInstance

end Map

end PolyhedralCone

-- namespace PolyhedralCone

-- variable {R M N : Type*}
--   [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
--   [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M]
--   [AddCommGroup N] [Module R N] -- [Module.Finite 𝕜 M]

-- instance : Bot (PolyhedralCone R M) := ⟨⊥, .bot⟩

-- instance uniqueBot : Unique (⊥ : PolyhedralCone R M) :=
--   inferInstanceAs <| Unique (⊥ : PointedCone R M)

-- instance : Top (PolyhedralCone R M) := ⟨ ⊤, .top ⟩

-- instance : Min (PolyhedralCone R M) where
--   min C C' := ⟨C ⊓ C', C.isPolyhedral.inf C'.isPolyhedral⟩

-- @[simp, norm_cast] lemma coe_inf (C D : PolyhedralCone R M) :
--     (C ⊓ D).toPointedCone = C.toPointedCone ⊓ D.toPointedCone := rfl

-- instance : SemilatticeInf (PolyhedralCone R M) :=
--   PolyhedralCone.toPointedCone_injective.semilatticeInf _ coe_inf

-- -- TODO: add simp lemmas

-- variable {𝕜 M N : Type*}
--   [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
--   [AddCommGroup M] [Module 𝕜 M] [Module.Finite 𝕜 M]
--   [AddCommGroup N] [Module 𝕜 N] -- [Module.Finite 𝕜 M]

-- def of_IsPolyhedral {C : PointedCone 𝕜 M} (hC : C.IsPolyhedral) : PolyhedralCone 𝕜 M := ⟨ C, hC ⟩
-- def of_fg {C : PointedCone 𝕜 M} (hC : C.FG) : PolyhedralCone 𝕜 M := of_IsPolyhedral (.of_fg 𝕜 hC)

-- def span {S : Set M} (hfin : S.Finite) : PolyhedralCone 𝕜 M := of_IsPolyhedral (.span hfin)

-- variable (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair]
-- variable [Module.Finite 𝕜 N]
-- variable {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜} [p.IsPerfPair]

-- instance : Max (PolyhedralCone 𝕜 M) where
--   max C C' := ⟨C ⊔ C', C.isPolyhedral.sup C'.isPolyhedral⟩

-- @[simp, norm_cast] lemma coe_sup (C D : PolyhedralCone 𝕜 M) :
--     (C ⊔ D).toPointedCone = C.toPointedCone ⊔ D.toPointedCone := rfl

-- instance : SemilatticeSup (PolyhedralCone 𝕜 M) :=
--   PolyhedralCone.toPointedCone_injective.semilatticeSup _ coe_sup

-- lemma dual_inf {C C' : PolyhedralCone 𝕜 M} : dual p (C ⊓ C') = dual p C ⊔ dual p C' :=
--   sorry

-- lemma dual_sup {C C' : PolyhedralCone 𝕜 M} : dual p (C ⊔ C') = dual p C ⊓ dual p C' :=
--   sorry

-- end PolyhedralCone

-- /- Lattice structure -/

-- namespace PolyhedralCone

-- variable [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M] {s : Set (Dual 𝕜 M)} {w : M}

-- def ofSubmodule (S : Submodule 𝕜 M) : PolyhedralCone 𝕜 M := ⟨ S, .submodule S ⟩

-- instance : Coe (Submodule 𝕜 M) (PolyhedralCone 𝕜 M) := ⟨ .ofSubmodule ⟩

-- instance completeLattice : CompleteLattice (PolyhedralCone 𝕜 M) :=
--   { (inferInstance : OrderTop (PolyhedralCone 𝕜 M)),
--     (inferInstance : OrderBot (PolyhedralCone 𝕜 M)) with
--     sup := fun a b ↦ sInf { x | a ≤ x ∧ b ≤ x }
--     le_sup_left := fun _ _ ↦ le_sInf' fun _ ⟨h, _⟩ ↦ h
--     le_sup_right := fun _ _ ↦ le_sInf' fun _ ⟨_, h⟩ ↦ h
--     sup_le := fun _ _ _ h₁ h₂ ↦ sInf_le' ⟨h₁, h₂⟩
--     inf := (· ⊓ ·)
--     le_inf := fun _ _ _ ↦ Set.subset_inter
--     inf_le_left := fun _ _ ↦ Set.inter_subset_left
--     inf_le_right := fun _ _ ↦ Set.inter_subset_right
--     sSup S := sInf {sm | ∀ s ∈ S, s ≤ sm}
--     le_sSup := fun _ _ hs ↦ le_sInf' fun _ hq ↦ by exact hq _ hs
--     sSup_le := fun _ _ hs ↦ sInf_le' hs
--     le_sInf := fun _ _ ↦ le_sInf'
--     sInf_le := fun _ _ ↦ sInf_le' }

-- end PolyhedralCone
