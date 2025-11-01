import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic


namespace PointedCone

namespace Face

variable {R M N : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

/-!
## Partial Order and Lattice on Faces
-/

instance partialOrder : PartialOrder (Face C) := inferInstance

example (F G : Face C) (h : F ≤ G) : (F : Set M) ≤ G := h

@[simp]
theorem toPointedCone_le_iff {F₁ F₂ : Face C} : F₁ ≤ F₂ ↔ F₁.toPointedCone ≤ F₂.toPointedCone := by
  constructor <;> intro h x xF₁ <;> exact h xF₁

/-!
### Infimum, supremum and lattice

-/

/-- The infimum of two faces `F₁, F₂` of `C` is the infimum of the submodules `F₁` and `F₂`. -/
def inf (F₁ F₂ : Face C) : Face C := ⟨F₁ ⊓ F₂, F₁.isFaceOf.inter F₂.isFaceOf⟩

instance : InfSet (Face C) := ⟨fun S =>
  { toSubmodule := C ⊓ sInf {s.1 | s ∈ S}
    isFaceOf := by
      constructor
      · exact fun _ sm => sm.1
      · simp; intros _ xc _ yc _ _ zfs zo
        simp [xc]; intros F Fs
        exact F.isFaceOf.left_mem_of_mem_openSegment xc yc (zfs F Fs) zo
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

end Semiring

/-!
## Complete Lattice

-/

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F : PointedCone R M} {s t : Set M}

/-- The top element of the partial order on faces of `C` is `C` itself. -/
instance : OrderTop (Face C) where
  top := C
  le_top F := F.isFaceOf.subset

instance nonempty {C : PointedCone R M} : Nonempty (Face C) := ⟨⊤⟩

instance inhabited {C : PointedCone R M} : Inhabited (Face C) := ⟨⊤⟩

/-- The face of a pointed cone `C` that is its lineal space. It contained in all faces of `C`. -/
def lineal : Face C := ⟨C.lineal, IsFaceOf.lineal C⟩

lemma lineal_le {C : PointedCone R M} (F : Face C) : lineal ≤ F := by
  intro x xl
  apply lineal_mem.mp at xl
  exact (IsFaceOf.iff_mem_of_add_mem.mp F.isFaceOf).2 x xl.1 (-x) xl.2 (by simp)

/-- The bottom element of the partial order on faces of `C` is `C.lineal`. -/
instance : OrderBot (Face C) where
  bot := lineal
  bot_le F := F.lineal_le

instance : BoundedOrder (Face C) where

instance : CompleteLattice (Face C) where

end Field

end Face

end PointedCone
