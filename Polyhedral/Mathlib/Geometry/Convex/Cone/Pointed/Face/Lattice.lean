/-
Copyright (c) 2025 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
public import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank

/-!
## Face

This file proves results about the face lattice of a pointed cone.

## Quotients

* `Face.quot`, denoted `C ⧸ F`. is the quotient of a cone `C` w.r.t. a face `F`.
* `Face.quotFace` is the face of `C ⧸ F` that corresponds to a given face `G` of `C`.
* `Face.fiverFace` is the face of `C` that corresponds to a given face `G` of `C ⧸ F`.

* `Face.quot_orderIso`: The isomorphism between a quotient's face lattice and the interval in
  the cone's face lattice above the face.
* `Face.embed_orderIso`: The isomorphism between a face's face lattice and the interval in the
  cone's face lattice below the face.
-/

@[expose] public section

open Submodule Function

variable {R M M₁ M₂ N : Type*}

@[expose] public section

namespace PointedCone

namespace Face

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M} {F F₁ F₂ : Face C}

@[simp, norm_cast]
theorem toPointedCone_eq_iff {F₁ F₂ : Face C} :
    F₁.toPointedCone = F₂.toPointedCone ↔ F₁ = F₂ := by
  constructor <;> intro h <;> try rw [mk.injEq] at *; exact h

@[simp]
theorem coe_toPointedCone {F : Face C} :
    ((F : PointedCone R M) : Set M) = F := rfl

abbrev span (F : Face C) : Submodule R M := .span R F.toPointedCone

noncomputable abbrev rank (F : Face C) : Cardinal := F.toPointedCone.rank

noncomputable abbrev finrank (F : Face C) : ℕ := F.toPointedCone.finrank

end Semiring

-- ## Quot and Fiber

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M} {F : Face C}

/-- The map with which one computes the quotient of a cone w.r.t. a face. -/
abbrev quotMap (F : Face C) := mkQ F.span

/-- The cone obtained by quotienting by the face's linear span. -/
abbrev quot (F : Face C) : PointedCone R (M ⧸ F.span) := .map F.quotMap C

scoped notation:50 C " ⧸ " F => Face.quot (C := C) F

-- TODO: replace `salientQuot` by `C ⧸ ⊥` throughout the repo.

-- # FIBER

/-- The face of `C` that corresponds to a given face of `C ⧸ F`. -/
def fiberFace (G : Face (C ⧸ F)) : Face C := by
  refine ⟨C ⊓ PointedCone.comap F.quotMap G, ?_⟩
  simpa [Face.quot, Face.quotMap] using
    (PointedCone.IsFaceOf.inf_comap_mkQ (G := C) (S := F.span) (H := G) G.isFaceOf)

@[simp]
lemma mem_fiberFace (G : Face (C ⧸ F)) (x : M) :
    x ∈ fiberFace G ↔ x ∈ C ∧ F.quotMap x ∈ G := by
  change x ∈ C ⊓ comap F.quotMap ↑G ↔ _; simp_all

/-- Faces of a quotient cone can be naturally interpreted as faces of the cone itself. -/
instance : CoeOut (Face F.quot) (Face C) := ⟨fiberFace⟩

lemma le_fiber (G : Face (C ⧸ F)) : F ≤ fiberFace G := by
  intro x xF
  simp only [mem_fiberFace, F.isFaceOf.le xF, mkQ_apply,
    (Quotient.mk_eq_zero F.span).mpr (mem_span_of_mem xF), true_and]
  simp [← Face.mem_toPointedCone]

@[simp]
lemma map_quotMap_fiberFace (G : Face (C ⧸ F)) : PointedCone.map F.quotMap (fiberFace G) = G := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_fiberFace G y).mp hy |>.2
  · intro hx
    obtain ⟨y, yC, rfl⟩ := PointedCone.mem_map.mp (G.isFaceOf.le hx)
    exact PointedCone.mem_map.mpr ⟨y, (mem_fiberFace G y).mpr ⟨yC, hx⟩, rfl⟩

lemma fiberFace_le_fiberFace_iff {G₁ G₂ : Face (C ⧸ F)} :
    fiberFace G₁ ≤ fiberFace G₂ ↔ G₁ ≤ G₂ where
  mp h x hx := by
    have hx' : x ∈ PointedCone.map F.quotMap (fiberFace G₁) := by
      simpa [map_quotMap_fiberFace] using hx
    have hx'' : x ∈ PointedCone.map F.quotMap (fiberFace G₂) := by
      rcases PointedCone.mem_map.mp hx' with ⟨y, hy, rfl⟩
      exact PointedCone.mem_map.mpr ⟨y, h hy, rfl⟩
    simpa [map_quotMap_fiberFace] using hx''
  mpr h x hx := by
    rcases (mem_fiberFace G₁ x).mp hx with ⟨hxC, hxG⟩
    exact (mem_fiberFace G₂ x).mpr ⟨hxC, h hxG⟩

lemma fiberFace_monotone : Monotone (fiberFace : Face (C ⧸ F) → Face C) :=
  fun _ _ h => fiberFace_le_fiberFace_iff.mpr h

end Ring

section DirectedOrderRing

variable [Ring R] [PartialOrder R] [IsDirectedOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C : PointedCone R M} {F G : Face C}

/-- The face of `C ⧸ F` that corresponds to a given face of `C`. -/
def quotFace (F G : Face C) : Face (C ⧸ F) := by
  refine ⟨PointedCone.map F.quotMap ((F ⊔ G : Face C) : PointedCone R M), ?_⟩
  have hle : ((F : Face C) : PointedCone R M) ≤ ((F ⊔ G : Face C) : PointedCone R M) :=
    show F ≤ F ⊔ G from le_sup_left
  simpa [Face.quot, Face.quotMap] using
    (PointedCone.IsFaceOf.quot (C := C) (F := ((F ⊔ G : Face C) : PointedCone R M))
      (S := F.span) (F ⊔ G).isFaceOf (Submodule.span_mono hle))

@[simp]
lemma quotFace_eq_map_quotMap_of_le (h : F ≤ G) :
    F.quotFace G = PointedCone.map F.quotMap G := by
  simp [quotFace, sup_eq_right.mpr h]

@[simp]
lemma fiberFace_quotFace_of_le {F G : Face C} (h : F ≤ G) : fiberFace (F.quotFace G) = G := by
  ext x
  constructor <;> intro hx
  · rcases (mem_fiberFace (F.quotFace G) x).mp hx with ⟨hxC, hxq⟩
    have hxq' : F.quotMap x ∈ PointedCone.map F.quotMap G := by
      change F.quotMap x ∈ (F.quotFace G : PointedCone R (M ⧸ F.span)) at hxq
      simpa [quotFace_eq_map_quotMap_of_le h] using hxq
    obtain ⟨y, hyG, hyq⟩ := PointedCone.mem_map.mp hxq'
    have hxy : x - y ∈ F.span := by
      rw [← Submodule.ker_mkQ F.span]
      change F.quotMap (x - y) = 0
      simp only [map_sub, mkQ_apply, hyq, sub_self]
    have hx_lin : x ∈ Submodule.span R (G : Set M) :=
      ((Submodule.span R (G : Set M)).sub_mem_iff_left (Submodule.subset_span hyG)).mp
        (Submodule.span_mono h hxy)
    rw [← mem_toPointedCone, Face.toPointedCone, ← G.isFaceOf.inf_span]
    exact ⟨hxC, hx_lin⟩
  · refine (mem_fiberFace (F.quotFace G) x).mpr ⟨G.isFaceOf.le hx, ?_⟩
    change F.quotMap x ∈ (F.quotFace G : PointedCone R (M ⧸ F.span))
    simpa [quotFace_eq_map_quotMap_of_le h] using
      (PointedCone.mem_map.mpr ⟨x, hx, rfl⟩ : F.quotMap x ∈ PointedCone.map F.quotMap G)

lemma fiberFace_quotFace (F G : Face C) : fiberFace (F.quotFace G) = F ⊔ G := by
  simpa [quotFace, sup_assoc, sup_left_comm, sup_comm] using
    (fiberFace_quotFace_of_le (F := F) (G := F ⊔ G) le_sup_left)

@[simp]
lemma quotFace_fiberFace (G : Face (C ⧸ F)) : F.quotFace (fiberFace G) = G := by
  rw [← Face.toPointedCone_eq_iff]
  rw [quotFace_eq_map_quotMap_of_le (le_fiber G)]
  rw [map_quotMap_fiberFace]

/-- The isomorphism between the face lattice of the quotient cone and the interval in the
face lattice of the cone above the face. -/
def quot_orderIso (F : Face C) : Face (C ⧸ F) ≃o Set.Ici F where
  toFun G := ⟨fiberFace G, le_fiber G⟩
  invFun G := F.quotFace G
  left_inv := quotFace_fiberFace
  right_inv G := by simp only [fiberFace_quotFace_of_le G.2]
  map_rel_iff' := by
    intro G G'
    exact fiberFace_le_fiberFace_iff

/-- The embedding of the face lattice of the quotient into the face lattice of the cone. -/
def quot_orderEmbed (F : Face C) : Face (C ⧸ F) ↪o Face C :=
  (quot_orderIso F).toOrderEmbedding.trans <| OrderEmbedding.subtype _

variable (C) in
/-- The isomorphism between the face lattice of the salient quotient and the face lattice of
the cone itself. -/
def salientQuot_orderIso : Face (C ⧸ ⊥) ≃o Face C :=
  (quot_orderIso ⊥).trans OrderIso.IciBot

end DirectedOrderRing

section LinearOrderRing

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M} {F : Face C}

lemma fiberFace_eq_iff (G : Face (C ⧸ F)) : F = fiberFace G ↔ G.toPointedCone = ⊥ := by
  constructor <;> intro h
  · ext x
    refine ⟨?_, fun hx => hx ▸ G.zero_mem⟩
    · intro hxG
      obtain ⟨c, hcC, hcx⟩ := PointedCone.mem_map.mp (G.isFaceOf.le hxG)
      have hcF : c ∈ F := h ▸ ⟨hcC, Submodule.mem_comap.mpr (hcx ▸ hxG)⟩
      have hczero : F.quotMap c = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span hcF)
      rw [Submodule.mem_bot, ← hcx, hczero]
  · simp only [fiberFace, quotMap, comap, h, comap_bot, LinearMap.ker_restrictScalars, ker_mkQ,
    ← toPointedCone_eq_iff]
    suffices C ⊓ restrictScalars { c // 0 ≤ c } F.span = F by symm; exact this
    convert F.isFaceOf.inf_span

lemma le_span_iff_le {G : Face C} : (F : PointedCone R M) ≤ G.span ↔ F ≤ G := by
  simp [IsFaceOf.le_span_iff_le F.isFaceOf.le G.isFaceOf]

end LinearOrderRing

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable {C : PointedCone R M} {F : Face C}

lemma toPointedCone_bot_eq_bot_of_salient (hC : Salient C) : (⊥ : Face C).toPointedCone = ⊥ := by
  simp [Face.lineal_eq_bot, Face.toPointedCone, salient_iff_lineal_bot.mp hC]

lemma bot_face_of_salient (hC : C.Salient) : F.toPointedCone = ⊥ ↔ F = ⊥ := by
  refine ⟨fun h => Face.ext (fun x => ?_),
    fun h => by simp [h, toPointedCone_bot_eq_bot_of_salient hC]⟩
  change x ∈ F.toPointedCone ↔ x ∈ (⊥ : Face C).toPointedCone
  simp [h, toPointedCone_bot_eq_bot_of_salient hC]

/-!
### Embed and restrict
-/

/-- The face of `C` obtained by embedding a face of a face of `C`. -/
def embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : Face C :=
    ⟨F₂, F₂.isFaceOf.trans F₁.isFaceOf⟩

/-- A face of a face of `C` coerces to a face of `C`. -/
instance {F : Face C} : CoeOut (Face (F : PointedCone R M)) (Face C) := ⟨Face.embed⟩

/-- The face of `F₁` obtained by intersecting `F₁` with another face of `C`. -/
def restrict (F₁ F₂ : Face C) : Face (F₁ : PointedCone R M) :=
  ⟨F₁ ⊓ F₂, ((F₁.isFaceOf.inf_left F₂.isFaceOf).isFaceOf_iff_le F₁.isFaceOf).mpr inf_le_left⟩

lemma embed_restrict (F₁ F₂ : Face C) : embed (F₁.restrict F₂) = F₁ ⊓ F₂ := rfl

lemma embed_restrict_of_le {F₁ F₂ : Face C} (hF : F₂ ≤ F₁) :
    embed (F₁.restrict F₂) = F₂ := by simp [embed_restrict, hF]

lemma restrict_embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) :
    F₁.restrict (embed F₂) = F₂ := by
  unfold restrict embed; congr
  simp only [inf_eq_right, toPointedCone_le_toPointedCone]
  exact (F₂.isFaceOf.isFaceOf_iff_le IsFaceOf.rfl).mp F₂.isFaceOf

lemma embed_le {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : F₂ ≤ F₁ := by
  rw [← restrict_embed F₂, embed_restrict]
  simp only [inf_le_left]

/-- The isomorphism between the face lattice of a face and the interval in the face
 lattice of the cone below the face. -/
def embed_orderIso (F : Face C) : Face (F : PointedCone R M) ≃o Set.Iic F where
  toFun G := ⟨G, Face.embed_le G⟩
  invFun G := F.restrict G
  left_inv := restrict_embed
  right_inv G := by simp only [embed_restrict_of_le G.2]
  map_rel_iff' := by
    intro G G'
    rfl

/-- The embedding of the face lattice of the face into the face lattice of the cone. -/
def embed_orderEmbed (F : Face C) : Face (F : PointedCone R M) ↪o Face C :=
  (embed_orderIso F).toOrderEmbedding.trans <| OrderEmbedding.subtype _

end DivisionRing

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]

variable {C : PointedCone R M₁}

-- # Map and comap

/-- The image of a face under a linear map as a face of the image of the cone. -/
def map {f : M₁ →ₗ[R] M₂} (hf : Injective f) (F : Face C) : Face (map f C) :=
  ⟨_, F.isFaceOf.map _ hf⟩

lemma map_inj (f : M₁ →ₗ[R] M₂) (hf : Injective f) :
    Injective (map hf : Face C → Face _) := by
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

/-- The image of a face under a linear equivalence as a face of the image of the cone. -/
def map_equiv (e : M₁ ≃ₗ[R] M₂) (F : Face C) : Face (.map (e : M₁ →ₗ[R] M₂) C) :=
  F.map e.injective

def map_orderIso {f : M₁ →ₗ[R] M₂} (hf : Injective f) :
    Face C ≃o Face (.map f C) where
  toFun := map hf
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry

/-- The preimage of a face under a linear map as a face of the preimage of the cone. -/
def comap {C : PointedCone R M₂} {f : M₁ →ₗ[R] M₂} (F : Face C) : Face (comap f C) :=
  ⟨_, F.isFaceOf.comap _⟩

/-- The preimage of a face under a linear equivalence as a face of the preimage of the cone. -/
def comap_equiv {C : PointedCone R M₂} (e : M₁ ≃ₗ[R] M₂) (F : Face C) :
    Face (.comap (e : M₁ →ₗ[R] M₂) C) :=
  F.comap

def comap_orderIso {C : PointedCone R M₂} {f : M₁ →ₗ[R] M₂} (hf : Surjective f) :
    Face C ≃o Face (.comap f C) where
  toFun := comap
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry

end Semiring

section Ring

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

def inf_isCompl_lineal_orderIso {S : Submodule R M} (hS : IsCompl C.lineal S) :
    Face (C ⊓ S) ≃o Face C := sorry

end Ring

end Face

end PointedCone
