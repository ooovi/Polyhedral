import Polyhedral.Mathlib.LinearAlgebra.ConvexSpace
import Mathlib.Analysis.Convex.Segment


open ConvexSpace

namespace ConvexSet

variable (R : Type*) {M : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M]

theorem refl (S : ConvexSet R M) : S.IsFaceOf S := by
  constructor
  · simp
  · intro x hx y hy z hz h
    apply hx

theorem openSegment_symm (x y : M) : openSegment R x y = openSegment R y x := by
  unfold ConvexSpace.openSegment
  ext z
  apply Iff.intro
  · intro h
    simp only [Set.mem_setOf_eq]
    rcases h with ⟨m, n, hm , hn , hmn , hz⟩
    use n, m, hn, hm
    rw [add_comm] at hmn
    use hmn
    unfold convexComboPair
    unfold convexCombination
    sorry
  · intro h
    simp only [Set.mem_setOf_eq]
    rcases h with ⟨m,n,hm,hn,hmn,hz⟩
    use n,m,hn,hm
    rw [add_comm] at hmn
    sorry

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

theorem intersection_convexsets (S₁ S₂ : ConvexSet R M) : Convex R  (S₁.carrier ∩ S₂.carrier ) := by
  have hs₁ := S₁.2
  have hs₂ := S₂.2
  unfold ConvexSpace.Convex at hs₁ hs₂
  unfold ConvexSpace.Convex
  intro x hx y hy a b ha hb h
  have hx1 := hx.1
  have hx2 := hx.2
  have hy1 := hy.1
  have hy2 := hy.2
  specialize @hs₁ x hx1 y hy1 a b ha hb h
  specialize @hs₂ x hx2 y hy2 a b ha hb h
  exact Set.mem_inter hs₁ hs₂

def Inter (A B : ConvexSet R M) : ConvexSet R M := {
  carrier := (A.carrier ∩ B.carrier),
  convex := by
    have h_sInter : Convex R (⋂₀ {A.carrier, B.carrier}) := by
      apply ConvexSpace.convex_sInter
      intro s hs
      rcases hs with rfl | rfl
      · exact A.convex
      · exact B.convex
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

end ConvexSet
