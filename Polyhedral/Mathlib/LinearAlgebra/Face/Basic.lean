import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic
import Mathlib.Analysis.Convex.Segment
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

open Convexity
open Affine Convexity

variable (R : Type*) {M N : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] [ConvexSpace R N]

namespace ConvexSet

/- S is a face of itself -/
theorem refl (S : ConvexSet R M) : S.IsFaceOf S :=
  ⟨by simp , by intro x hx y hy z hz h; apply hx⟩

/- (x,y)=(y,x) -/
theorem openSegment_symm (x y : M) : openSegment R x y = openSegment R y x := by
  unfold Convexity.openSegment
  ext z
  constructor
  all_goals (intro h; rcases h with ⟨m, n, hm , hn , hmn , hz⟩; use n, m, hn, hm)
  all_goals (rw [convexCombPair_symm] at hz; rw [add_comm] at hmn; use hmn)

/- transitivity of faces -/
theorem trans (S F₁ F₂ : ConvexSet R M) (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf S) :
F₂.IsFaceOf S := by
  constructor
  · apply Set.Subset.trans h₁.1 h₂.1
  · intro x hx y hy z hz hhz
    have hz' : z ∈ F₁.carrier := Set.mem_of_mem_of_subset hz h₁.1
    exact @h₁.2 x (@h₂.2 x hx y hy z hz' hhz) y (@h₂.2 y hy x hx z hz' (by simpa [openSegment_symm]
    using hhz)) z hz hhz

/- smaller faces are faces of bigger faces -/
theorem iff_le_of_isFaceOf (S F₁ F₂ : ConvexSet R M) (h₁ : F₁.IsFaceOf S)
  (h₂ : F₂.IsFaceOf S) :
F₁.IsFaceOf F₂ ↔ F₁.carrier ⊆ F₂.carrier := by
  constructor
  · exact fun h => h.1
  · intro hh
    constructor
    · exact hh
    · intro x hx y hy z hz hhz
      exact h₁.2 (Set.mem_of_mem_of_subset hx h₂.1) (Set.mem_of_mem_of_subset hy h₂.1) hz hhz

/-A convex set is a face of a face iff it is contained in the face and it is a face
of the ambient set-/
lemma isFaceOf_iff (F C F₁ : ConvexSet R M) (H : F.IsFaceOf C) :
F₁.IsFaceOf F ↔ F₁.carrier ⊆ F.carrier ∧ F₁.IsFaceOf C:= by
  apply Iff.intro
  · exact fun h => ⟨h.1, trans R C F F₁ h H⟩
  · intro h
    constructor
    · apply h.1
    · intro x hx y hy z hz hhz
      exact @h.2.2 x (Set.mem_of_mem_of_subset hx H.1) y (Set.mem_of_mem_of_subset hy H.1) z hz hhz

/-intersection of two convex sets is a convex set -/
theorem intersection_convexsets (S₁ S₂ : ConvexSet R M) : IsConvexSet R  (S₁.carrier ∩ S₂.carrier )
:= by
  intro w hw
  rw [Set.subset_inter_iff] at hw
  exact ⟨@S₁.2 w hw.1, @S₂.2 w hw.2⟩

/- definition of intersection of convex sets -/
def Inter (A B : ConvexSet R M) : ConvexSet R M := {
  carrier := (A.carrier ∩ B.carrier),
  isConvexSet := by
    have h_sInter : IsConvexSet R (⋂₀ {A.carrier, B.carrier}) := by
      apply Convexity.IsConvexSet.sInter
      intro s hs
      rcases hs with rfl | rfl
      · exact A.isConvexSet
      · exact B.isConvexSet
    exact Set.sInter_pair A.carrier B.carrier ▸ h_sInter
  }

/-The intersection of two faces of two convexsets is a face of the intersection of the convexsets-/
theorem inf (S₁ S₂ F₁ F₂ : ConvexSet R M) (h₁ : F₁.IsFaceOf S₁) (h₂ : F₂.IsFaceOf S₂) :
(Inter R F₁ F₂).IsFaceOf (Inter R S₁ S₂) := by
  constructor
  · rw [@Set.subset_def]
    exact fun x hx => ⟨Set.mem_of_mem_of_subset hx.1 h₁.1, Set.mem_of_mem_of_subset hx.2 h₂.1⟩
  · intro a ha b hb z hz hhz
    exact ⟨@h₁.2 a ha.1 b hb.1 z hz.1 hhz, @h₂.2 a ha.2 b hb.2 z hz.2 hhz⟩

/- The intersection of two faces is a face.-/
theorem inf_left (S F₁ F₂ : ConvexSet R M) (h₁ : F₁.IsFaceOf S) (h₂ : F₂.IsFaceOf S) :
(Inter R F₁ F₂).IsFaceOf S := by
  constructor
  · simpa [Set.inter_self] using Set.inter_subset_inter h₁.1 h₂.1
  · intro x hx y hy z hz hhz
    exact ⟨@h₁.2 x hx y hy z hz.1 hhz, @h₂.2 x hx y hy z hz.2 hhz⟩

/- The face of two convexsets is a face of the intersection.-/
theorem inf_right (S₁ S₂ F : ConvexSet R M) (h₁ : F.IsFaceOf S₁) (h₂ : F.IsFaceOf S₂) :
F.IsFaceOf (Inter R S₁ S₂) :=
  ⟨Set.subset_inter h₁.1 h₂.1, by intro x hx y hy z hz hhz; exact @h₁.2 x hx.1 y hy.1 z hz hhz⟩

/- The image of a face under an injective affine map is a face. -/
theorem map {f : M → N} (hhf : IsAffineMap R f) (hf : Function.Injective f)
  (F C : ConvexSet R M) (hF : F.IsFaceOf C) : (F.map hhf).IsFaceOf (C.map hhf) := by
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

/- defiition of preimage of a convex set -/
def comap {f : M → N} (hf : IsAffineMap R f) (C : ConvexSet R N) : ConvexSet R M := {
  carrier := f ⁻¹' C.carrier,
  isConvexSet := by apply Convexity.IsConvexSet.preimage hf C.isConvexSet
}

/- The preimage of a face is a face -/
theorem comap_face {f : M → N} (hf : IsAffineMap R f) (F C : ConvexSet R N)
 (hF : F.IsFaceOf C) : (F.comap hf).IsFaceOf (C.comap hf) := by
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

/- F is a face of C iff the image of F is a face of the image of C under an injective affine map -/
theorem isFaceOf_map_iff_2 (f : M → N) (hhf : IsAffineMap R f) (hf : Function.Injective f)
(C F : ConvexSet R M):(F.map hhf).IsFaceOf (C.map hhf) ↔ F.IsFaceOf C := by
  apply Iff.intro
  · intro h
    have hh:= comap_face R hhf (F.map hhf) (C.map hhf) h
    have h (A: ConvexSet R M) : (A.map hhf).comap hhf = A := by
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
    apply map R hhf hf F C h

end ConvexSet
