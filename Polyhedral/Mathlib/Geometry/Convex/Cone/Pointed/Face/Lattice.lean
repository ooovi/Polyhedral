/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Dual

import Mathlib.LinearAlgebra.Quotient.Defs


/-!
## Face

This file defines the notion of face of a pointed cone as a bundled object and establishes the
complete lattice structure thereon. The type `Face C` therefore also represents the face lattice
of a pointed cone `C`.

## Main definitions

* `Face C`: the face lattice of `C`.
* `inf` and `sup`: infimum and supremum operations on `Face C`.
* `CompleteLattice` instance: the face lattice of a pointed cone using `inf` and `sup`.
* `prod`: the product of two faces of pointed cones, together with projections `prod_left` and
  `prod_right`.
* `prod_orderIso`: proves that the face lattices of a product cone is the product of the face
  lattices of the individual cones.

-/

@[expose] public section

namespace PointedCone

variable {R M N : Type*}


variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M] in
/-- A face of a pointed cone `C`. Represents the face lattice of `C`. -/
structure Face (C : PointedCone R M) extends PointedCone R M where
  isFaceOf : IsFaceOf toSubmodule C

namespace Face

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C C₁ C₂ : PointedCone R M} {F F₁ F₂ : Face C}

/-- Converts a face of a pointed cone into a pointed cone. -/
@[coe]
abbrev toPointedCone {C : PointedCone R M} (F : Face C) : PointedCone R M := F.toSubmodule

instance : CoeOut (Face (C : PointedCone R M)) (PointedCone R M) := ⟨toPointedCone⟩

instance : SetLike (Face C) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp <| by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

instance : PartialOrder (Face C) := .ofSetLike (Face C) M

@[ext]
theorem ext (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

@[simp]
theorem coe_le_iff {F₁ F₂ : Face C} : F₁.toPointedCone ≤ F₂.toPointedCone ↔ F₁ ≤ F₂ := by
  constructor <;> intro h x xF₁ <;> exact h xF₁

@[simp]
theorem mem_coe {F : Face C} (x : M) : x ∈ F.toPointedCone ↔ x ∈ F := .rfl

/-!
### Infimum, supremum and lattice
-/

/-- The infimum of two faces `F₁`, `F₂` of `C` is the intersection of the cones `F₁` and `F₂`. -/
instance : Min (Face C) where
  min F₁ F₂ := ⟨F₁ ⊓ F₂, F₁.isFaceOf.inf_left F₂.isFaceOf⟩

instance : InfSet (Face C) where
  sInf S :=
    { toSubmodule := C ⊓ sInf {s.1 | s ∈ S}
      isFaceOf := by
        refine ⟨fun _ sm => sm.1, ?_⟩
        simp only [Submodule.mem_inf, Submodule.mem_sInf, Set.mem_setOf_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂]
        intros _ _ a xc yc a0 _ h
        simpa [xc] using fun F Fs => F.isFaceOf.mem_of_smul_add_mem xc yc a0 (h F Fs)
    }

instance : SemilatticeInf (Face C) where
  inf := min
  inf_le_left _ _ _ xi := xi.1
  inf_le_right _ _ _ xi := xi.2
  le_inf _ _ _ h₁₂ h₂₃ _ xi := ⟨h₁₂ xi, h₂₃ xi⟩

instance : CompleteSemilatticeInf (Face C) where
  __ := instSemilatticeInf
  sInf_le S f fS := by
    rw [← coe_le_iff]
    refine inf_le_of_right_le ?_
    simpa [LE.le] using fun _ xs => xs f fS
  le_sInf S f fS := by
    simp only [sInf, Set.mem_setOf_eq, Set.iInter_exists, Set.biInter_and',
      Set.iInter_iInter_eq_right, ← coe_le_iff, toPointedCone, le_inf_iff]
    refine ⟨f.isFaceOf.le, ?_⟩
    simpa [LE.le] using fun _ xf s sm => fS s sm xf

instance : CompleteLattice (Face C) where
  top := ⟨C, IsFaceOf.refl _⟩
  le_top F := F.isFaceOf.le
  __ := completeLatticeOfCompleteSemilatticeInf _

instance : Inhabited (Face C) := ⟨⊤⟩

instance : Nonempty (Face C) := ⟨⊤⟩

instance : CompleteLattice (Face C) where


end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {C C₁ : PointedCone R M} {C₂ : PointedCone R N}

lemma lineal_bot : (⊥ : Face C) = ⟨_, IsFaceOf.lineal C⟩ :=
   le_antisymm bot_le (IsFaceOf.lineal_le (⊥ : Face C).isFaceOf)

/-- The lineality space of a cone `C` as a face of `C`. It is contained in all faces of `C`. This is
an abbrev for `⊥`. -/
abbrev lineal : Face C := ⊥

/-!
### Product
-/
section Prod

open Submodule

/-- The face of `C₁ × C₂` obtained by taking the (submodule) product of faces `F₁ ≤ C₁` and
`F₂ ≤ C₂`. -/
def prod (F₁ : Face C₁) (F₂ : Face C₂) : Face (C₁.prod C₂) := ⟨_, F₁.isFaceOf.prod F₂.isFaceOf⟩

/-- The face of `C₁` obtained by projecting to the first component of a face `F ≤ C₁ × C₂`. -/
def fst (F : Face (C₁.prod C₂)) : Face C₁ := ⟨_, F.isFaceOf.fst⟩

/-- The face of `C₁` obtained by projecting to the second component of a face `F ≤ C₁ × C₂`. -/
def snd (F : Face (C₁.prod C₂)) : Face C₂ := ⟨_, F.isFaceOf.snd⟩

@[simp]
theorem prod_fst (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).fst = F₁ := by
  ext
  simpa [fst, prod, ← mem_coe, toPointedCone] using fun _ => ⟨0, F₂.toSubmodule.zero_mem⟩

@[simp]
theorem prod_snd (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).snd = F₂ := by
  ext
  simpa [snd, prod, ← mem_coe, toPointedCone] using fun _ => ⟨0, F₁.toSubmodule.zero_mem⟩

theorem fst_prod_snd (G : Face (C₁.prod C₂)) : G.fst.prod G.snd = G := by
  ext x
  simp only [prod, fst, snd, ← mem_coe, toPointedCone, mem_prod, mem_map, LinearMap.fst_apply,
    Prod.exists, exists_and_right, exists_eq_right, LinearMap.snd_apply]
  constructor
  · simp only [and_imp, forall_exists_index]
    intro y yn z zm
    have := add_mem zm yn
    simp only [Prod.mk_add_mk, add_comm] at this
    rw [← Prod.mk_add_mk, add_comm] at this
    refine G.isFaceOf.mem_of_add_mem ?_ ?_ this
    · exact ⟨(mem_prod.mp (G.isFaceOf.le yn)).1, (mem_prod.mp (G.isFaceOf.le zm)).2⟩
    · exact ⟨(mem_prod.mp (G.isFaceOf.le zm)).1, (mem_prod.mp (G.isFaceOf.le yn)).2⟩
  · intro h; exact ⟨⟨x.2, h⟩, ⟨x.1, h⟩⟩

@[gcongr]
theorem prod_mono {F₁ F₁' : Face C₁} {F₂ F₂' : Face C₂} :
    F₁ ≤ F₁' → F₂ ≤ F₂' → prod F₁ F₂ ≤ prod F₁' F₂' := Submodule.prod_mono

/-- The face lattice of the product of two cones is isomorphic to the product of their face
lattices. -/
def prodOrderIso (C : PointedCone R M) (D : PointedCone R N) :
    Face (C.prod D) ≃o Face C × Face D where
  toFun G := ⟨fst G, snd G⟩
  invFun G := G.1.prod G.2
  left_inv G := by simp [fst_prod_snd]
  right_inv G := by simp
  map_rel_iff' := by
    simp only [Equiv.coe_fn_mk, ge_iff_le, Prod.mk_le_mk]
    intro F₁ F₂; constructor <;> intro a
    · simpa [fst_prod_snd, coe_le_iff] using Face.prod_mono a.1 a.2
    · constructor; all_goals
      try simpa only [prod_left, prod_right]
      exact fun _ d => Submodule.map_mono a d

end Prod

end Field



end Face

end PointedCone


-----------------------end of PR










namespace PointedCone

variable {R M N : Type*}

namespace Face

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C C₁ C₂ : PointedCone R M} {F F₁ F₂ : Face C}

@[simp, norm_cast]
theorem toPointedCone_eq_iff {F₁ F₂ : Face C} :
    F₁.toPointedCone = F₂.toPointedCone ↔ F₁ = F₂ := by
  constructor <;> intro h <;> try rw [mk.injEq] at *; exact h

abbrev span (F : Face C) : Submodule R M := Submodule.span R F

end Semiring


section Ring

open Submodule hiding span dual IsDualClosed

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C : PointedCone R M}

-- ## QUOT / FIBER

abbrev quotMap (F : Face C) := mkQ F.span
-- abbrev IsFaceOf.quot {C F : PointedCone R M} (hF : F.IsFaceOf C) := C.quot (Submodule.span R F)

-- lemma IsFaceOf.quot {C F₁ F₂ : PointedCone R M} (hF₁ : F₁.IsFaceOf C) (hF₂ : F₂.IsFaceOf C)
--     (hF : F₂ ≤ F₁) : (F₁.quot F₂.linSpan).IsFaceOf (C.quot F₂.linSpan) := by
--   sorry

-- def quotBy (C : PointedCone R M) (F : Face C) : PointedCone R (M ⧸ F.span) := map F.quotMap C

/-- The cone obtained by quotienting by the face's linear span. -/
abbrev quot (F : Face C) : PointedCone R (M ⧸ F.span) := .map F.quotMap C

def quotFace (F G : Face C) : Face (F.quot) :=
    ⟨F.quot ⊓ PointedCone.map F.quotMap G,
     ⟨by simp, fun x' y' h0 ha => by sorry⟩⟩

def fiberFace {F : Face C} (G : Face (F.quot)) : Face C :=
    ⟨C ⊓ PointedCone.comap F.quotMap G, by sorry⟩

/-- Faces of a quotient cone can naturally be considered as faces of the cone. -/
instance {F : Face C} : CoeOut (Face F.quot) (Face C) := ⟨fiberFace⟩

lemma fiber_quot (F G : Face C) : fiberFace (F.quotFace G) = F ⊔ G := sorry

lemma fiber_quot_of_le {F G : Face C} (h : F ≤ G) : fiberFace (F.quotFace G) = G :=
     by simp [fiber_quot, h]

lemma quot_fiber {F : Face C} (G : Face (F.quot)) : F.quotFace (fiberFace G) = G := sorry

lemma le_fiber {F : Face C} (G : Face (F.quot)) : F ≤ fiberFace G := sorry

/-- The isomorphism between a quotient's face lattice and the interval in the cone's face
 lattice above the face. -/
def quot_orderIso (F : Face C) : Face F.quot ≃o Set.Icc F ⊤ where
  toFun G := ⟨G, le_fiber G, le_top⟩
  invFun G := F.quotFace G
  left_inv := quot_fiber
  right_inv G := by simp only [fiber_quot_of_le G.2.1]
  map_rel_iff' := by intro G G'; simp; sorry

def quot_orderEmbed (F : Face C) : Face F.quot ↪o Face C := sorry

end Ring


section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {C₁ : PointedCone R M} {C₂ : PointedCone R N}
variable {C F : PointedCone R M} {s t : Set M}


/-!
### Rank
-/

noncomputable def rank (F : Face C) := Module.rank R F.span

lemma bot_iff_rank_zero {F : Face C} (hC : C.Salient) : F.rank = 0 ↔ F = ⊥ := by
  have hEq : ((F : PointedCone R M) = (⊥ : PointedCone R M)) ↔ F = ⊥ := by
    simpa only [Face.lineal_bot, PointedCone.salient_iff_lineal_bot.mp hC] using
      (Face.toPointedCone_eq_iff (F₁ := F) (F₂ := (⊥ : Face C)))
  simpa [Face.rank, PointedCone.rank] using
    (PointedCone.bot_iff_rank_zero (C := (F : PointedCone R M))).trans hEq


/-!
### Embed and restrict
-/

/-- The face of `C` obtained by embedding a face of a face of `C`. -/
def embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : Face C :=
    ⟨F₂, F₂.isFaceOf.trans F₁.isFaceOf⟩

/-- A face of a face of `C` coerces to a face of `C`. -/
instance {F : Face C} : CoeOut (Face (F : PointedCone R M)) (Face C) := ⟨Face.embed⟩

/-- The face of `F₁` obtained by intersecting `F₁` with another of `C`'s faces. -/
def restrict (F₁ F₂ : Face C) : Face (F₁ : PointedCone R M) :=
  ⟨F₁ ⊓ F₂, ((F₁.isFaceOf.inf_left F₂.isFaceOf).iff_le_of_isFaceOf F₁.isFaceOf).mpr inf_le_left⟩

lemma embed_restrict (F₁ F₂ : Face C) : embed (F₁.restrict F₂) = F₁ ⊓ F₂ := rfl

lemma embed_restrict_of_le {F₁ F₂ : Face C} (hF : F₂ ≤ F₁) :
    embed (F₁.restrict F₂) = F₂ := by simp [embed_restrict, hF]

lemma restrict_embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) :
    F₁.restrict (embed F₂) = F₂ := by
  unfold restrict embed; congr
  simpa using F₂.isFaceOf.le

lemma embed_le {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : F₂ ≤ F₁ := by
  rw [← restrict_embed F₂, embed_restrict]
  simp only [inf_le_left]

/-- The isomorphism between a face's face lattice and the interval in the cone's face
 lattice below the face. -/
def embed_orderIso (F : Face C) : Face (F : PointedCone R M) ≃o Set.Icc ⊥ F where
  toFun G := ⟨G, bot_le, Face.embed_le G⟩
  invFun G := F.restrict G
  left_inv := restrict_embed
  right_inv G := by simp only [embed_restrict_of_le G.2.2]
  map_rel_iff' := @fun _ _ => by simp [embed]; sorry

/-- The embedding of a face's face lattice into the cone's face lattice. -/
def embed_orderEmbed (F : Face C) : Face (F : PointedCone R M) ↪o Face C :=
  (embed_orderIso F).toOrderEmbedding.trans <| OrderEmbedding.subtype _


variable (p : M →ₗ[R] N →ₗ[R] R)

/-- The face of the dual cone that corresponds to this face. -/
def dual (F : Face C) : Face (dual p C) := ⟨_, F.isFaceOf.subdual_dual p⟩

def dual_flip (hC : DualClosed p C) (F : Face (.dual p C)) : Face C :=
  ⟨subdual p.flip (.dual p C) F, by
    nth_rw 2 [← LinearMap.flip_flip p]
    rw [← dual_flip_dual_dual_flip]
    simp only [LinearMap.flip_flip, dual_dual_flip_dual]
    convert F.isFaceOf.subdual_dual (p.flip)
    exact (DualClosed.def p hC).symm
  ⟩

lemma dual_antitone : Antitone (dual p : Face C → Face _) :=
  fun _ _ hF _ xd => subdual_antitone p hF xd

-- not sure if these are necessary
/-!
#### Map and comap
-/
/-- The face `map f F` of `map f C`. -/
def map {f : M →ₗ[R] N} (hf : Function.Injective f) (F : Face C) : Face (map f C)
    := ⟨_, F.isFaceOf.map _ hf⟩

lemma map_inj (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (map hf : Face C → Face _) := by
  intro F₁ F₂ h
  simp only [map, mk.injEq] at h
  ext x; constructor <;> intro hx
  · have : f x ∈ PointedCone.map f F₁.toSubmodule := mem_map.mpr ⟨x, ⟨hx, rfl⟩⟩
    rw [h] at this
    obtain ⟨y, yF₂, fy⟩ := Submodule.mem_map.mp this
    simpa [← hf fy]
  · have : f x ∈ PointedCone.map f F₂.toSubmodule := mem_map.mpr ⟨x, ⟨hx, rfl⟩⟩
    rw [← h] at this
    obtain ⟨y, yF₂, fy⟩ := Submodule.mem_map.mp this
    simpa [← hf fy]

/-- The face `map e F` of `map e C`. -/
def map_equiv (e : M ≃ₗ[R] N) (F : Face C) : Face (PointedCone.map (e : M →ₗ[R] N) C)
    := F.map e.injective

/-- The face `comap f F` of `comap f C`. -/
def comap {f : N →ₗ[R] M} (F : Face C) : Face (comap f C) := ⟨_, F.isFaceOf.comap _⟩

-- /-- The face `comap e F` of `comap e C`. -/
-- def comap_equiv (e : N ≃ₗ[R] M) (F : Face C) : Face (PointedCone.comap (e : N →ₗ[R] M) C)
--     := F.comap

end Field

end Face

end PointedCone

end
