/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic

/-!
## Face

This file defines a bundled object for a face of a pointed cone and a complete lattice structure on
them.

## Main definitions

* `Face C`: a bundled structure for a face of the pointed cone `C`.
* `inf` and `sup`: infimum and supremum operations on `Face C`
* `Lattice` instance: the face lattice of a pointed cone using `inf` and `sup`.
* `prod`: the product of two faces of pointed cones, together with projections `prod_left` and
  `prod_right`.
* `prod_orderIso`: the order isomorphism defined by `prod`.

-/

@[expose] public section

namespace PointedCone

variable {R M N : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
in
/-- A face of a pointed cone `C`, as a bundled structure. -/
structure Face (C : PointedCone R M) extends PointedCone R M where
  isFaceOf : IsFaceOf toSubmodule C

namespace Face

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C C₁ C₂ : PointedCone R M} {F F₁ F₂ : Face C}

/-- A pointed cone `C` as a face of itself. -/
def self (C : PointedCone R M) : Face C := ⟨C, IsFaceOf.refl _⟩

instance {C : PointedCone R M} : CoeDep (PointedCone R M) C (Face C) :=
  ⟨Face.self C⟩

/- Convert a face of a pointed cone into a pointed cone. -/
@[coe, simp]
def toPointedCone {C : PointedCone R M} (F : Face C) : PointedCone R M := F.toSubmodule

instance : CoeOut (Face (C : PointedCone R M)) (PointedCone R M) where
  coe := toPointedCone

instance : SetLike (Face C) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp <| by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

@[ext]
theorem ext (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

@[simp]
theorem toPointedCone_le_iff {F₁ F₂ : Face C} : F₁ ≤ F₂ ↔ F₁.toPointedCone ≤ F₂.toPointedCone := by
  constructor <;> intro h x xF₁ <;> exact h xF₁

@[simp]
theorem mem_toPointedCone {F : Face C} (x : M) : x ∈ F ↔ x ∈ F.toPointedCone := .rfl

/-!
### Infimum, supremum and lattice
-/

/-- The infimum of two faces `F₁, F₂` of `C` is the infimum of the cones `F₁` and `F₂`. -/
def inf (F₁ F₂ : Face C) : Face C := ⟨F₁ ⊓ F₂, F₁.isFaceOf.inf_left F₂.isFaceOf⟩

instance : InfSet (Face C) :=
⟨fun S =>
  { toSubmodule := C ⊓ sInf {s.1 | s ∈ S}
    isFaceOf := by
      constructor
      · exact fun _ sm => sm.1
      · simp only [Submodule.mem_inf, Submodule.mem_sInf, Set.mem_setOf_eq, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂]
        intros _ _ a xc yc a0 _ h
        simp only [xc, true_and]; intros F Fs
        exact F.isFaceOf.mem_of_smul_add_mem xc yc a0 (h F Fs)
}⟩

instance : SemilatticeInf (Face C) where
  inf := inf
  inf_le_left _ _ _ xi := xi.1
  inf_le_right _ _ _ xi := xi.2
  le_inf _ _ _ h₁₂ h₂₃ _ xi := ⟨h₁₂ xi, h₂₃ xi⟩

instance : CompleteSemilatticeInf (Face C) where
  __ := instSemilatticeInf
  sInf_le S f fS := by
    simp only [toPointedCone_le_iff, toPointedCone]
    refine inf_le_of_right_le ?_
    simp only [LE.le, Submodule.mem_sInf, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro x xs
    exact xs f fS
  le_sInf S f fS := by
    simp only [sInf, Set.mem_setOf_eq, Set.iInter_exists, Set.biInter_and',
      Set.iInter_iInter_eq_right, toPointedCone_le_iff, toPointedCone, le_inf_iff]
    refine ⟨f.isFaceOf.le, ?_⟩
    simp only [LE.le, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_iInter,
      SetLike.mem_coe]
    intro x xf s sm
    exact fS s sm xf

/-- The supremum of two faces `F₁, F₂` of `C` is the smallest face of `C` that has both `F₁` and
`F₂` as faces. -/
def sup (F₁ F₂ : Face C) : Face C := sInf {F : Face C | F₁ ≤ F ∧ F₂ ≤ F}

instance : SemilatticeSup (Face C) where
  sup := sup
  le_sup_left _ _ := le_sInf (fun _ Fs => Fs.1)
  le_sup_right _ _ := le_sInf (fun _ Fs => Fs.2)
  sup_le _ _ _ h₁₂ h₂₃ := sInf_le (Set.mem_sep h₁₂ h₂₃)

/-- `sSup S` of a set `S` of faces of `C` is the smallest face of `C` that has all members of `S` as
faces. -/
instance : SupSet (Face C) := ⟨fun (S : Set (Face C)) => sInf { F : Face C | ∀ F' ∈ S, F' ≤ F}⟩

instance : CompleteSemilatticeSup (Face C) where
  __ := instSemilatticeSup
  sSup := sSup
  sSup_le _ _ fS := sInf_le_of_le fS le_rfl
  le_sSup _ f fS := le_sInf_iff.mpr <| fun _ a ↦ a f fS

instance : Lattice (Face C) where

/-- The top element of the partial order on faces of `C` is `C` itself. -/
instance : OrderTop (Face C) where
  top := C
  le_top F := F.isFaceOf.le

instance : Inhabited (Face C) := ⟨⊤⟩

instance : Nonempty (Face C) := ⟨⊤⟩

/-!
### `OrderHom` for some operations
-/

/-- Mapping a face `F₁` of `C₁` to the face `F₁ ⊓ F₂ ≤ C₁ ⊓ C₂` for some face `F₂` of `C₂` preserves
the face lattice. -/
def face_inf_orderHom (F₂ : Face C₂) : Face C₁ →o Face (C₁ ⊓ C₂) where
  toFun F := ⟨_, F.isFaceOf.inf F₂.isFaceOf⟩
  monotone' F₁ F₂ h x := by
    simp only [mem_toPointedCone, toPointedCone, Submodule.mem_inf,
    and_imp]; exact fun xF₁ xC₂ => ⟨h.subset xF₁, xC₂⟩

/-- Mapping a face `F` of `C₁` to the face `F ⊓ C₂ ≤ C₁ ⊓ C₂` preserves the face lattice. -/
def inf_orderHom (C₂ : PointedCone R M) : Face C₁ →o Face (C₁ ⊓ C₂) :=
  face_inf_orderHom (self C₂)

/-- Mapping the product of faces `F₁ ≤ C₁` and `F₂ ≤ C₂` to the face `F₁ ⊓ F₂ ≤ C₁ ⊓ C₂` preserves
the face lattice. -/
def prod_face_inf_orderHom : Face C₁ × Face C₂ →o Face (C₁ ⊓ C₂) where
  toFun F := ⟨_, F.1.isFaceOf.inf F.2.isFaceOf⟩
  monotone' F₁ F₂ h x := by
    simp only [mem_toPointedCone, toPointedCone, Submodule.mem_inf, and_imp]
    intros xF₁ xF₂
    simp only [LE.le, mem_toPointedCone, toPointedCone] at h
    exact ⟨h.1 xF₁, h.2 xF₂⟩

end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {C₁ : PointedCone R M} {C₂ : PointedCone R N}

/-!
### Product
-/
section Prod

-- TODO make IsFaceOf lemmas

open Submodule

/-- The face of `C₁ × C₂` obtained by taking the (submodule) product of faces `F₁ ≤ C₁` and
`F₂ ≤ C₂`. -/
def prod (F₁ : Face C₁) (F₂ : Face C₂) : Face (C₁.prod C₂) := by
  refine ⟨Submodule.prod F₁ F₂, ⟨?_, ?_⟩⟩
  · intro x xp
    rw [Submodule.mem_prod] at xp ⊢
    exact ⟨F₁.isFaceOf.le xp.1, F₂.isFaceOf.le xp.2⟩
  · simp only [Submodule.mem_prod, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, and_imp, Prod.forall]
    intro _ _ _ _ _ xc₁ xc₂ yc₁ yc₂ a0 hab₁ hab₂
    constructor
    · exact F₁.isFaceOf.mem_of_smul_add_mem xc₁ yc₁ a0 hab₁
    · exact F₂.isFaceOf.mem_of_smul_add_mem xc₂ yc₂ a0 hab₂

/-- The face of `C₁` obtained by projecting to the left component of a face `F ≤ C₁ × C₂`. -/
def prod_left (F : Face (C₁.prod C₂)) : Face C₁ := {
  map (LinearMap.fst _ M N) F with
  isFaceOf := by sorry
    -- constructor
    -- · intro x xm
    --   simp [LinearMap.fst_apply] at xm
    --   convert (Set.mem_prod.mp <| F.isFaceOf.le xm.choose_spec).1
    -- · simp only [toPointedCone, mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right,
    --   exists_eq_right, forall_exists_index]
    --   intro x y _ xc yc a0 z h
    --   use 0
    --   refine F.isFaceOf.mem_of_smul_add_mem (x := (x, 0)) (y := (y, b⁻¹ • z)) ?_ ?_ a0 ?_
    --   · exact mem_prod.mp ⟨xc, zero_mem C₂⟩
    --   · exact mem_prod.mp ⟨yc, smul_mem C₂ (le_of_lt (inv_pos_of_pos b0)) (F.isFaceOf.le h).2⟩
    --   · simpa [← smul_assoc, mul_inv_cancel₀ (ne_of_lt b0).symm]
}

/-- The face of `C₂` obtained by projecting to the right component of a face `F ≤ C₁ × C₂`. -/
def prod_right (F : Face (C₁.prod C₂)) : Face C₂ := {
  map (LinearMap.snd _ M N) F with
  isFaceOf := by sorry
    -- constructor
    -- · intro x xm
    --   simp [LinearMap.snd_apply] at xm
    --   convert (Set.mem_prod.mp <| F.isFaceOf.le xm.choose_spec).2
    -- · simp only [toPointedCone, mem_map, LinearMap.snd_apply, Prod.exists, exists_eq_right,
    --   forall_exists_index]
    --   intro x y _ b xc yc a0 b0 z h
    --   use 0
    --   refine F.isFaceOf.left_mem_of_smul_add_mem (x := (0, x)) (y := (b⁻¹ • z, y)) ?_ ?_ a0 b0 ?_
    --   · exact mem_prod.mp ⟨zero_mem C₁, xc⟩
    --   · exact mem_prod.mp ⟨smul_mem C₁ (le_of_lt (inv_pos_of_pos b0)) (F.isFaceOf.le h).1, yc⟩
    --   · simpa [← smul_assoc, mul_inv_cancel₀ (ne_of_lt b0).symm]
  }

@[simp]
theorem prod_prod_left (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).prod_left = F₁ := by
  ext
  simp only [prod_left, toPointedCone, prod, mem_toPointedCone, mem_map, mem_prod,
    LinearMap.fst_apply, Prod.exists, exists_and_right, exists_and_left, exists_eq_right,
    and_iff_left_iff_imp]
  exact fun _ => ⟨0, F₂.toSubmodule.zero_mem⟩

@[simp]
theorem prod_prod_right (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).prod_right = F₂ := by
  ext
  simp only [prod_right, toPointedCone, prod, mem_toPointedCone, mem_map, mem_prod,
    LinearMap.snd_apply, Prod.exists, exists_eq_right, exists_and_right, and_iff_right_iff_imp]
  exact fun _ => ⟨0, F₁.toSubmodule.zero_mem⟩

theorem prod_left_prod_right (G : Face (C₁.prod C₂)) : G.prod_left.prod G.prod_right = G := by
  ext x
  simp only [prod, toPointedCone, prod_left, prod_right, mem_toPointedCone, mem_prod, mem_map,
    LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right, LinearMap.snd_apply]
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

theorem prod_mono {F₁ F₁' : Face C₁} {F₂ F₂' : Face C₂} :
  F₁ ≤ F₁' → F₂ ≤ F₂' → prod F₁ F₂ ≤ prod F₁' F₂' :=
  Submodule.prod_mono

/- The face lattice of the product of two cones is isomorphic to the product of their face
lattices. -/
def prod_orderIso (C : PointedCone R M) (D : PointedCone R N) :
    Face (C.prod D) ≃o Face C × Face D where
  toFun G := ⟨prod_left G, prod_right G⟩
  invFun G := G.1.prod G.2
  left_inv G := by simp [prod_left_prod_right]
  right_inv G := by simp
  map_rel_iff' := by
    simp only [Equiv.coe_fn_mk, ge_iff_le, Prod.mk_le_mk, toPointedCone_le_iff, toPointedCone]
    intro F₁ F₂; constructor <;> intro a
    · have := Face.prod_mono a.1 a.2
      simp only [prod_left_prod_right, toPointedCone_le_iff, toPointedCone] at this
      exact this
    · constructor; all_goals
      try simp only [prod_left, prod_right]
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

-- instance {S : Submodule R M} : CoeDep (Submodule R M) S (Face (S : PointedCone R M)) :=
--   ⟨(S : PointedCone R M)⟩

@[simp, norm_cast]
theorem toPointedCone_eq_iff {F₁ F₂ : Face C} :
    F₁.toPointedCone = F₂.toPointedCone ↔ F₁ = F₂ := by
  constructor <;> intro h <;> try rw [mk.injEq] at *; exact h


end Semiring


/-!
### Complete Lattice
needs lineal
-/
-- commented out because there are problems with imports
-- section Field

-- variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
--   [AddCommGroup N] [Module R N] {C C₁ F : PointedCone R M} {C₂ : PointedCone R N}

-- /-- The face of a pointed cone `C` that is its lineal space. It is contained in all faces of `C`. -/
-- def lineal {C : PointedCone R M} : Face C := ⟨C.lineal, IsFaceOf.lineal C⟩

-- lemma lineal_le {C : PointedCone R M} (F : Face C) : lineal ≤ F := F.isFaceOf.lineal_le

-- /-- The bottom element of the partial order on faces of `C` is `C.lineal`. -/
-- instance : OrderBot (Face C) where
--   bot := lineal
--   bot_le F := F.lineal_le

-- instance : BoundedOrder (Face C) where

-- instance : CompleteLattice (Face C) where

-- end Field

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {C₁ : PointedCone R M} {C₂ : PointedCone R N}
variable {C F : PointedCone R M} {s t : Set M}

-- can't define the order embeddin until we have the complete lattice
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
  ⟨F₁ ⊓ F₂, (F₁.isFaceOf.inf_left F₂.isFaceOf).iff_le F₁.isFaceOf inf_le_left⟩

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

-- /-- The isomorphism between a face's face lattice and the interval in the cone's face
--  lattice below the face. -/
-- def embed_orderIso (F : Face C) : Face (F : PointedCone R M) ≃o Set.Icc ⊥ F where
--   toFun G := ⟨G, bot_le, Face.embed_le G⟩
--   invFun G := F.restrict G
--   left_inv := restrict_embed
--   right_inv G := by simp only [embed_restrict_of_le G.2.2]
--   map_rel_iff' := @fun _ _ => by simp [embed]

-- /-- The embedding of a face's face lattice into the cone's face lattice. -/
-- def embed_orderEmbed (F : Face C) : Face (F : PointedCone R M) ↪o Face C :=
--   (embed_orderIso F).toOrderEmbedding.trans <| OrderEmbedding.subtype _


-- needs dual

abbrev span (F : Face C) : Submodule R M := Submodule.span R F

variable (p : M →ₗ[R] N →ₗ[R] R)

-- /-- The face of the dual cone that corresponds to this face. -/
-- def dual (F : Face C) : Face (dual p C) := ⟨_, F.isFaceOf.subdual_dual p⟩

-- def Face.dual_flip (F : Face (.dual p C)) : Face C := ⟨subdual p.flip (.dual p C) F, by
--   nth_rw 2 [← LinearMap.flip_flip p]
--   exact F.isFaceOf.subdual_dual
--   ⟩

-- lemma dual_antitone : Antitone (dual p : Face C → Face _) :=
--   fun _ _ hF _ xd => subdual_antitone p (toPointedCone_le_iff.mpr hF) xd

-- not sure if these are necessary
/-!
#### Map and comap
-/
/-- The face `map f F` of `map f C`. -/
def map {f : M →ₗ[R] N} (hf : Function.Injective f) (F : Face C) : Face (map f C)
    := ⟨_, F.isFaceOf.map hf⟩

lemma map_inj (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (map hf : Face C → Face _) := by
  intro F₁ F₂ h
  simp [map] at h
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
def comap {f : N →ₗ[R] M} (F : Face C) : Face (comap f C) := ⟨_, F.isFaceOf.comap⟩

-- /-- The face `comap e F` of `comap e C`. -/
-- def comap_equiv (e : N ≃ₗ[R] M) (F : Face C) : Face (PointedCone.comap (e : N →ₗ[R] M) C)
--     := F.comap

end Field

end Face

end PointedCone

end
