/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Mara Gruß, Valentina Taylor Cerra, Martin Winter
-/

import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Mathlib.Analysis.Convex.Segment
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

/-! This file defines faces of convex sets.

NOTE: Currently this file is still aligned with the old convexity API of mathlib, defining
`openSegment` and `IsExtreme`. This will later be refactored. Please only use `IsFaceOf` and
avoid using the legacy API.
-/

variable {R M N : Type*}

section Semiring

-- Eventually, most of the below will become global names
namespace Convexity

variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
variable [ConvexSpace R M] [ConvexSpace R N]

-- the following is copied from the mathlib convexity def and adapted to ours

variable (R) in
/-- Open segment in a convex space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def openSegment (x y : M) : Set M :=
  { z : M | ∃ (a b : R) (a0 : 0 < a) (b0 : 0 < b) (ab : a + b = 1),
    convexCombPair a b a0.le b0.le ab x y = z }

/- (x,y) = (y,x) -/
theorem openSegment_symm (x y : M) : openSegment R x y = openSegment R y x := by
  ext z
  constructor
  all_goals (intro h; rcases h with ⟨m, n, hm , hn , hmn , hz⟩; use n, m, hn, hm)
  all_goals (rw [convexCombPair_symm] at hz; rw [add_comm] at hmn; use hmn)

/- NOTE: This is *legacy API* -/
/- TODO: This is a temporary construction to align faces with the current mathlib implementation
of `IsExtreme`. This will be removed soon. -/
variable (R) in
/-- A set `B` is an extreme subset of `A` if `B ⊆ A` and all points of `B` only belong to open
segments whose ends are in `B`.

Our definition only requires that the left endpoint of the segment lies in `B`,
but by symmetry of open segments, the right endpoint must also lie in `B`. -/
@[mk_iff]
structure IsExtreme (A B : Set M) : Prop where
  subset : B ⊆ A
  left_mem_of_mem_openSegment : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A →
    ∀ ⦃z⦄, z ∈ B → z ∈ openSegment R x y → x ∈ B

theorem isExtreme_empty {C : Set M} : IsExtreme R C ∅ where
  subset := C.empty_subset
  left_mem_of_mem_openSegment := by simp

namespace ConvexSet

/- NOTE: maybe this should be defined on `Set` instead of `ConvexSet`. -/
/-- A subset `F` of a convex set `C` is a face of `C` iff it is an extreme subset. -/
def IsFaceOf (F C : ConvexSet R M) := IsExtreme R C (F : Set M)

namespace IsFaceOf

/- A convex set is a face of itself. -/
theorem refl (C : ConvexSet R M) : C.IsFaceOf C :=
  ⟨by simp , by intro x hx y hy z hz h; apply hx⟩

/- The face relation is transitive. -/
theorem trans {C F₁ F₂ : ConvexSet R M} (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) :
    F₂.IsFaceOf C := by
  constructor
  · apply Set.Subset.trans h₁.1 h₂.1
  · intro x hx y hy z hz hhz
    have hz' : z ∈ F₁.carrier := Set.mem_of_mem_of_subset hz h₁.1
    exact @h₁.2 x (@h₂.2 x hx y hy z hz' hhz) y (@h₂.2 y hy x hx z hz' (by simpa [openSegment_symm]
    using hhz)) z hz hhz

/- For two faces `F₁, F₂` of `C`, `F₁` is a face of `F₂` iff it is a subset of `F₂`. -/
theorem iff_le_of_isFaceOf {C F₁ F₂ : ConvexSet R M} (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁.carrier ⊆ F₂.carrier := by
  constructor
  · exact fun h => h.1
  · intro hh
    constructor
    · exact hh
    · intro x hx y hy z hz hhz
      exact h₁.2 (Set.mem_of_mem_of_subset hx h₂.1) (Set.mem_of_mem_of_subset hy h₂.1) hz hhz

/- A convex set is a face of a face iff it is contained in the face and it is a face
of the ambient set. -/
lemma isFaceOf_iff {F C : ConvexSet R M} (F₁ : ConvexSet R M) (H : F.IsFaceOf C) :
    F₁.IsFaceOf F ↔ F₁.carrier ⊆ F.carrier ∧ F₁.IsFaceOf C:= by
  apply Iff.intro
  · exact fun h => ⟨h.1, trans h H⟩
  · intro h
    constructor
    · apply h.1
    · intro x hx y hy z hz hhz
      exact @h.2.2 x (Set.mem_of_mem_of_subset hx H.1) y (Set.mem_of_mem_of_subset hy H.1) z hz hhz

/- The intersection of two faces of two convex sets is a face of the intersection of the convex
sets. -/
theorem inf {S₁ S₂ F₁ F₂ : ConvexSet R M} (h₁ : F₁.IsFaceOf S₁) (h₂ : F₂.IsFaceOf S₂) :
    (F₁ ⊓ F₂).IsFaceOf (S₁ ⊓ S₂) := by
  constructor
  · rw [@Set.subset_def]
    exact fun x hx => ⟨Set.mem_of_mem_of_subset hx.1 h₁.1, Set.mem_of_mem_of_subset hx.2 h₂.1⟩
  · intro a ha b hb z hz hhz
    exact ⟨@h₁.2 a ha.1 b hb.1 z hz.1 hhz, @h₂.2 a ha.2 b hb.2 z hz.2 hhz⟩

/- The intersection of two faces is a face. -/
theorem inf_left {C F₁ F₂ : ConvexSet R M} (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    (F₁ ⊓ F₂).IsFaceOf C := by
  constructor
  · simpa [Set.inter_self] using Set.inter_subset_inter h₁.1 h₂.1
  · intro x hx y hy z hz hhz
    exact ⟨@h₁.2 x hx y hy z hz.1 hhz, @h₂.2 x hx y hy z hz.2 hhz⟩

/- The face of two convex sets is a face of the intersection. -/
theorem inf_right {S₁ S₂ F : ConvexSet R M} (h₁ : F.IsFaceOf S₁) (h₂ : F.IsFaceOf S₂) :
    F.IsFaceOf (S₁ ⊓ S₂) :=
  ⟨Set.subset_inter h₁.1 h₂.1, by intro x hx y hy z hz hhz; exact @h₁.2 x hx.1 y hy.1 z hz hhz⟩

/- The image of a face under an injective affine map is a face of the image. -/
theorem map {f : M → N} {F C : ConvexSet R M} (hhf : IsAffineMap R f) (hf : Function.Injective f)
    (hF : F.IsFaceOf C) : (F.map hhf).IsFaceOf (C.map hhf) := by
  constructor
  · intro x hx
    rcases hx with ⟨y , hy, rfl⟩
    exact Set.mem_image_of_mem _ (Set.mem_of_mem_of_subset hy hF.1)
  · intro x hx y hy z hz hhz
    rcases hx with ⟨m , hmC, rfl⟩
    rcases hy with ⟨n , hnC, rfl⟩
    rcases hz with ⟨l , hlF, rfl⟩
    have hl : l ∈ Convexity.openSegment R m n := by
      rcases hhz with ⟨ a, b, ha, hb, hab, hcomb⟩
      have h : f (convexCombPair a b ha.le hb.le hab m n) =
      convexCombPair a b ha.le hb.le hab (f m) (f n) := hhf.map_convexCombPair ha.le hb.le hab m n
      have hh : f (convexCombPair a b ha.le hb.le hab m n) = f l := by
        simpa [h] using hcomb
      exact ⟨ a, b, ha, hb, hab, hf hh⟩
    exact Set.mem_image_of_mem _ (@hF.2 m hmC n hnC l hlF hl)

/- The preimage of a face is a face of the preimage. -/
theorem comap_face {f : M → N} {F C : ConvexSet R N} (hf : IsAffineMap R f) (hF : F.IsFaceOf C) :
   (F.comap hf).IsFaceOf (C.comap hf) := by
  constructor
  · apply Set.preimage_mono hF.1
  · have hF1 := hF.2
    intro x hx y hy z hz hhz
    have hhz' : f z ∈ Convexity.openSegment R (f x) (f y) := by
      rcases hhz with ⟨ a, b, ha, hb, hab, hcomb⟩
      have hff : f (convexCombPair a b ha.le hb.le hab x y) =
        convexCombPair a b ha.le hb.le hab (f x) (f y) := hf.map_convexCombPair ha.le hb.le hab x y
      rw [hcomb] at hff
      use a, b, ha, hb, hab, hff.symm
    specialize @hF1 (f x) (Set.mem_preimage.mp hx ) (f y) (Set.mem_preimage.mp hy) (f z) (
      Set.mem_preimage.mp hz) hhz'
    apply Set.mem_preimage.mp hF1

/- `F` is a face of `C` iff the image of `F` is a face of the image of `C` under an injective affine
map -/
theorem isFaceOf_map_iff {f : M → N} {F C : ConvexSet R M} (hhf : IsAffineMap R f)
    (hf : Function.Injective f) :
    (F.map hhf).IsFaceOf (C.map hhf) ↔ F.IsFaceOf C := by
  constructor
  · intro h
    have hh := comap_face hhf h
    have h (A : ConvexSet R M) : (A.map hhf).comap hhf = A := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨y, hy, hzy⟩
        rw [hf hzy] at hy
        use hy
      · intro hz
        have hhz : f z ∈ (A.map hhf) := by
          use z, hz
        apply Set.mem_preimage.mp hhz
    rw [h F, h C] at hh
    exact hh
  · intro h
    apply map hhf hf h

end IsFaceOf

/- NOTE: maybe this should be defined on `Set` instead of `ConvexSet`. -/
/-- A face of a convex set `P`. Represents the face lattice of `P`. -/
structure Face (P : ConvexSet R M) extends toConvexSet : ConvexSet R M where
  isFaceOf : IsFaceOf toConvexSet P

namespace Face

variable {P : ConvexSet R M}

instance : SetLike (Face P) M where
  coe F := F.toConvexSet.carrier
  coe_injective a b h := by
    cases a; cases b; congr; exact SetLike.coe_injective h

@[simp] theorem carrier_eq_coe {F : Face P} : F.carrier = F := by rfl

@[simp] theorem mem_coe {F : Face P} (x : M) : x ∈ F.carrier ↔ x ∈ F := .rfl

@[ext] theorem ext {F₁ F₂ : Face P} (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

@[simp] theorem coe_eq_toConvexSet_coe {F : Face P} : (F : Set M) = F.toConvexSet :=
  SetLike.ext'_iff.mp rfl

instance : PartialOrder (Face P) := .ofSetLike ..

instance : Bot (Face P) :=
  ⟨⟨∅, .empty⟩, by simp [IsFaceOf, ← ConvexSet.carrier_eq_coe, isExtreme_empty]⟩

lemma nonempty_of_ne_bot {F : Face P} (h : F ≠ ⊥) : (F : Set M).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro heq
  apply h
  ext
  simp [← SetLike.mem_coe, heq, Bot.bot]

end Convexity.ConvexSet.Face

end Semiring
