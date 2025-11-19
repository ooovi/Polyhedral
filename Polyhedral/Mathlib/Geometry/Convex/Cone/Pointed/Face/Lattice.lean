import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic


namespace PointedCone

namespace Face

variable {R M N : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] {C C₁ C₂ F F₁ F₂ : PointedCone R M}

/-!
### Infimum, supremum and lattice
-/

/-- The infimum of two faces `F₁, F₂` of `C` is the infimum of the submodules `F₁` and `F₂`. -/
def inf (F₁ F₂ : Face C) : Face C := ⟨F₁ ⊓ F₂, F₁.isFaceOf.inf_left F₂.isFaceOf⟩

instance : InfSet (Face C) := ⟨fun S =>
  { toSubmodule := C ⊓ sInf {s.1 | s ∈ S}
    isFaceOf := by
      constructor
      · exact fun _ sm => sm.1
      · simp; intros _ _ a b xc yc a0 b0 _ h
        simp [xc]; intros F Fs
        exact F.isFaceOf.left_mem_of_smul_add_mem xc yc a0 b0 (h F Fs)
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
    simp [LE.le]
    intro x xs
    exact xs f fS
  le_sInf S f fS := by
    simp [sInf]
    refine ⟨f.isFaceOf.subset, ?_⟩
    simp [LE.le]
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
def sSup (S : Set (Face C)) : Face C := sInf { F : Face C | ∀ F' ∈ S, F' ≤ F}

instance : SupSet (Face C) :=
  ⟨fun S => {
    carrier := sSup S
    add_mem' aS bS := Submodule.add_mem _ aS bS
    zero_mem' := Submodule.zero_mem _
    smul_mem' _ _ h := Submodule.smul_mem _ _ h
    isFaceOf := (sSup S).isFaceOf
  }⟩

instance : CompleteSemilatticeSup (Face C) where
  __ := instSemilatticeSup
  sSup := sSup
  sSup_le _ _ fS := sInf_le_of_le fS le_rfl
  le_sSup _ f fS := le_sInf_iff.mpr <| fun _ a ↦ a f fS

instance : Lattice (Face C) where

/-!
### `OrderHom` for some operations
-/

/-- Mapping a face `F₁` of `C₁` to the face `F₁ ⊓ F₂ ≤ C₁ ⊓ C₂` for some face `F₂` of `C₂` preserves
the face lattice. -/
def face_inf_orderHom (F₂ : Face C₂) : Face C₁ →o Face (C₁ ⊓ C₂) where
  toFun F := ⟨_, F.isFaceOf.inf F₂.isFaceOf⟩
  monotone' F₁ F₂ h x := by simp; exact fun xF₁ xC₂ => ⟨h.subset xF₁, xC₂⟩

/-- Mapping a face `F` of `C₁` to the face `F ⊓ C₂ ≤ C₁ ⊓ C₂` preserves the face lattice. -/
def inf_orderHom (C₂ : PointedCone R M) : Face C₁ →o Face (C₁ ⊓ C₂) :=
  face_inf_orderHom (self C₂)

/-- Mapping the product of faces `F₁ ≤ C₁` and `F₂ ≤ C₂` to the face `F₁ ⊓ F₂ ≤ C₁ ⊓ C₂` preserves
the face lattice. -/
def prod_face_inf_orderHom : Face C₁ × Face C₂ →o Face (C₁ ⊓ C₂) where
  toFun F := ⟨_, F.1.isFaceOf.inf F.2.isFaceOf⟩
  monotone' F₁ F₂ h x := by
    simp
    intros xF₁ xF₂
    simp [LE.le] at h
    exact ⟨h.1 xF₁, h.2 xF₂⟩

/-!
### Complete Lattice
-/

/-- The top element of the partial order on faces of `C` is `C` itself. -/
instance : OrderTop (Face C) where
  top := C
  le_top F := F.isFaceOf.subset

instance nonempty {C : PointedCone R M} : Nonempty (Face C) := ⟨⊤⟩

instance inhabited {C : PointedCone R M} : Inhabited (Face C) := ⟨⊤⟩

end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
  {C F : PointedCone R M} {s t : Set M}

def prod_orderIso (C : PointedCone R M) (D : PointedCone R N) :
    Face (C.prod D) ≃o Face C × Face D where
  toFun G := ⟨prod_left G, prod_right G⟩
  invFun G := G.1.prod G.2
  left_inv G := by sorry
  right_inv G := by simp [prod_left, prod_right, prod]; sorry
  map_rel_iff' := sorry

lemma lineal_le {C : PointedCone R M} (F : Face C) : lineal ≤ F := F.isFaceOf.lineal_le

-- lemma lineal_le' {C F : PointedCone R M} (hF : F.IsFaceOf C) : C.lineal ≤ F := lineal_le ⟨F, hF⟩

/-- The bottom element of the partial order on faces of `C` is `C.lineal`. -/
instance : OrderBot (Face C) where
  bot := lineal
  bot_le F := F.lineal_le

instance : BoundedOrder (Face C) where

instance : CompleteLattice (Face C) where

/-!
### Embed and restrict
-/

lemma embed_restrict (F₁ F₂ : Face C) : embed (F₁.restrict F₂) = F₁ ⊓ F₂ := rfl

lemma embed_restrict_of_le {F₁ F₂ : Face C} (hF : F₂ ≤ F₁) :
    embed (F₁.restrict F₂) = F₂ := by simp [embed_restrict, hF]

lemma restrict_embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) :
    F₁.restrict (embed F₂) = F₂ := by
  unfold restrict embed; congr
  simpa using F₂.isFaceOf.subset

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
  map_rel_iff' := @fun _ _ => by simp [embed]

/-- The embedding of a face's face lattice into the cone's face lattice. -/
def embed_orderEmbed (F : Face C) : Face (F : PointedCone R M) ↪o Face C :=
  (embed_orderIso F).toOrderEmbedding.trans <| OrderEmbedding.subtype _

end Field

end Face

end PointedCone
