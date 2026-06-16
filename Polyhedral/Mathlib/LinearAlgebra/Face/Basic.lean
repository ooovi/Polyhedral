import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Face.Basic
import Mathlib.Analysis.Convex.Segment
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

open Convexity
open Affine Convexity

variable (R : Type*) {M N : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] [ConvexSpace R N]

namespace ConvexSet

theorem refl (S : ConvexSet R M) : S.IsFaceOf S := by
  constructor
  · simp
  · intro x hx y hy z hz h
    apply hx

theorem openSegment_symm (x y : M) : openSegment R x y = openSegment R y x := by
  unfold Convexity.openSegment
  ext z
  apply Iff.intro
  · intro h
    rcases h with ⟨m, n, hm , hn , hmn , hz⟩
    use n, m, hn, hm
    rw [convexCombPair_symm] at hz
    rw [add_comm] at hmn
    use hmn
  · intro h
    rcases h with ⟨m, n, hm , hn , hmn , hz⟩
    use n, m, hn, hm
    rw [convexCombPair_symm] at hz
    rw [add_comm] at hmn
    use hmn

theorem trans (S F₁ F₂ : ConvexSet R M) (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf S) :
F₂.IsFaceOf S := by
  have H₁ := h₁.2
  have H₂ := h₂.2
  constructor
  · apply Set.Subset.trans h₁.1 h₂.1
  · intro x hx y hy z hz hhz
    have hhhz : z ∈ F₁.carrier := Set.mem_of_mem_of_subset hz h₁.1
    have HH₂ := @H₂ x hx y hy z hhhz hhz
    have hh := hhz
    rw [openSegment_symm] at hh
    have HHH₂ := @H₂ y hy x hx z hhhz hh
    specialize @H₁ x HH₂ y HHH₂ z hz hhz
    apply H₁

theorem iff_le_of_isFaceOf (S F₁ F₂ : ConvexSet R M) (h₁ : F₁.IsFaceOf S) (h₂ : F₂.IsFaceOf S) :
F₁.IsFaceOf F₂ ↔ F₁.carrier ⊆ F₂.carrier := by
  constructor
  · intro h
    apply h.1
  · intro hh
    constructor
    · apply hh
    · intro x hx y hy z hz hhz
      have hhx : x ∈ S.carrier := Set.mem_of_mem_of_subset hx h₂.1
      have hhy : y ∈ S.carrier := Set.mem_of_mem_of_subset hy h₂.1
      have hh₁ := h₁.2
      specialize hh₁ hhx hhy hz hhz
      apply hh₁

/-A convex set is a face of a face iff it is contained in the face and it is a face
of the ambient set-/
lemma isFaceOf_iff (F C F₁ : ConvexSet R M) (H : F.IsFaceOf C) :
F₁.IsFaceOf F ↔ F₁.carrier ⊆ F.carrier ∧ F₁.IsFaceOf C:= by
  apply Iff.intro
  · intro h
    constructor
    · apply h.1
    · apply trans R C F F₁ h H
  · intro h
    constructor
    · apply h.1
    · have h₁ := h.2.2
      intro x hx y hy z hz hhz
      have hhx : x ∈ C.carrier := Set.mem_of_mem_of_subset hx H.1
      have hhy : y ∈ C.carrier := Set.mem_of_mem_of_subset hy H.1
      specialize @h₁ x hhx y hhy z hz hhz
      use h₁

/-intersection of two convex sets is a convex set -/
theorem intersection_convexsets (S₁ S₂ : ConvexSet R M) : IsConvexSet R  (S₁.carrier ∩ S₂.carrier )
:= by
  have hs₁ := S₁.2
  have hs₂ := S₂.2
  unfold Convexity.IsConvexSet at hs₁ hs₂
  unfold Convexity.IsConvexSet
  intro w hw
  rw [Set.subset_inter_iff] at hw
  specialize @hs₁ w hw.1
  specialize @hs₂ w hw.2
  use hs₁

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
    intro x hx
    have hhx := hx.1
    have hhhx := hx.2
    constructor
    · apply Set.mem_of_mem_of_subset hhx h₁.1
    · apply Set.mem_of_mem_of_subset hhhx h₂.1
  · intro a ha b hb z hz hhz
    have ha1 := ha.1
    have hb1 := hb.1
    have hz1 := hz.1
    have ha2 := ha.2
    have hb2 := hb.2
    have hz2 := hz.2
    have hh1 := h₁.2
    have hh2 := h₂.2
    specialize @hh1 a ha.1 b hb.1 z hz.1 hhz
    specialize @hh2 a ha.2 b hb.2 z hz.2 hhz
    constructor
    · use hh1
    · use hh2

/- The intersection of two faces is a face.-/
theorem inf_left (S F₁ F₂ : ConvexSet R M) (h₁ : F₁.IsFaceOf S) (h₂ : F₂.IsFaceOf S) :
(Inter R F₁ F₂).IsFaceOf S := by
  have hh1 := h₁.1
  have hh2 := h₂.1
  constructor
  · have hhh := Set.inter_subset_inter hh1 hh2
    rw[Set.inter_self] at hhh
    unfold Inter
    use hhh
  · intro x hx y hy z hz hhz
    have h1 := h₁.2
    have h2 := h₂.2
    specialize @h1 x hx y hy z hz.1 hhz
    specialize @h2 x hx y hy z hz.2 hhz
    use h1
    use h2

/- The face of two convexsets is a face of the intersection.-/
theorem inf_right (S₁ S₂ F : ConvexSet R M) (h₁ : F.IsFaceOf S₁) (h₂ : F.IsFaceOf S₂) :
F.IsFaceOf (Inter R S₁ S₂) := by
  constructor
  · have hh1 := h₁.1
    have hh2 := h₂.1
    apply Set.subset_inter
    · use hh1
    · use hh2
  · intro x hx y hy z hz hhz
    have h1 := h₁.2
    specialize @h1 x hx.1 y hy.1 z hz hhz
    use h1

/- The image of a face under an injective affine map is a face. -/
theorem map {f : M → N} (hhf : IsAffineMap R f) (hf : Function.Injective f) (F C : ConvexSet R M)
  (hF : F.IsFaceOf C) :
  (F.map hhf).IsFaceOf (C.map hhf) := by
  constructor
  · have hF1 := hF.1
    intro x hx
    rcases hx with ⟨y , hy, rfl⟩
    have hy1 : y ∈ C.carrier := Set.mem_of_mem_of_subset hy hF1
    apply Set.mem_image_of_mem
    use hy1
  · intro x hx y hy z hz hhz
    rcases hx with ⟨m , hmC, rfl⟩
    rcases hy with ⟨n , hnC, rfl⟩
    rcases hz with ⟨l , hlF, rfl⟩
    have hl : l ∈ Convexity.openSegment R m n := by
      rcases hhz with ⟨ a, b, ha, hb, hab, hcomb⟩
      have hfcomb := (hhf.map_sConvexComb)
      have h : f (convexCombPair a b ha.le hb.le hab m n) =
      convexCombPair a b ha.le hb.le hab (f m) (f n) := hhf.map_convexCombPair ha.le hb.le hab m n
      have hh : f (convexCombPair a b ha.le hb.le hab m n) = f l := by
        simpa [h] using hcomb
      exact ⟨ a, b, ha, hb, hab, hf hh⟩
    have hF2 := hF.2
    specialize @hF2 m hmC n hnC l hlF hl
    apply Set.mem_image_of_mem
    use hF2

/- F is a face of C iff the image of F is a face of the image of C under and injective affine map -/
theorem isFaceOf_map_iff (f : M → N) (hhf : IsAffineMap R f) (hf : Function.Injective f)
(C F : ConvexSet R M):(F.map hhf).IsFaceOf (C.map hhf) ↔ F.IsFaceOf C := by
  apply Iff.intro
  · intro h
    constructor
    · have h₁ := h.1
      have h' := (Set.image_subset_image_iff hf).mp h₁
      use h'
    · intro x hx y hy z hz hhz
      have hx' : f x ∈ (C.map hhf) := Set.mem_image_of_mem f hx
      have hy' : f y ∈ (C.map hhf) := Set.mem_image_of_mem f hy
      have hz' : f z ∈ (F.map hhf) := Set.mem_image_of_mem f hz
      have hhz' : f z ∈ Convexity.openSegment R (f x) (f y) := by
        rcases hhz with ⟨ a, b, ha, hb, hab, hcomb⟩
        have hff : f (convexCombPair a b ha.le hb.le hab x y) =
        convexCombPair a b ha.le hb.le hab (f x) (f y) := hhf.map_convexCombPair ha.le hb.le hab x y
        rw [hcomb] at hff
        unfold Convexity.openSegment
        use a, b, ha, hb, hab
        use hff.symm
      have h2 := h.2
      specialize @h2 (f x) hx' (f y) hy' (f z) hz' hhz'
      exact (Function.Injective.mem_set_image hf).mp h2
  · intro h
    apply map R hhf hf F C h

def comap {f : M → N} (hf : IsAffineMap R f) (C : ConvexSet R N) : ConvexSet R M := {
  carrier := f ⁻¹' C.carrier,
  isConvexSet := by apply Convexity.IsConvexSet.preimage hf C.isConvexSet
}

theorem of_comap_surjective {f : M → N} (hf : IsAffineMap R f) (hhf : Function.Surjective f) (F C : ConvexSet R N)
(hF : (F.comap hf).IsFaceOf (C.comap hf)) : F.IsFaceOf C := by
  constructor
  · have hF1 := hF.1
    have h1 : f '' (F.comap hf).carrier = F.carrier := by
      apply Set.image_preimage_eq F hhf
    have h2 : f '' (C.comap hf).carrier = C.carrier := by
      apply Set.image_preimage_eq C hhf
    have hF1' : f '' (F.comap hf).carrier ⊆ f '' (C.comap hf).carrier := by
    sorry
  · have hF1 := hF.2

    sorry

end ConvexSet
