import Mathlib.LinearAlgebra.ConvexSpace
import Mathlib.Order.Closure
import Mathlib.Order.OmegaCompletePartialOrder

section Convex

-- Eventually, most of the below will become global names
namespace ConvexSpace

variable {R : Type*} {M : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M]

-- TODO: rename to `IsConvex`

variable (R) in
/-- A set is convex if it contains all convex combinations of any two of its points. -/
def Convex (s : Set M) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : R⦄ (hs : 0 ≤ a) (ht : 0 ≤ b) (h : a + b = 1),
    convexComboPair a b hs ht h x y ∈ s

theorem convex_sInter {S : Set (Set M)} (h : ∀ s ∈ S, Convex R s) : Convex R (⋂₀ S) :=
  fun _ xs _ ys _ _ hs ht h1 t ts =>
    h t ts ((Set.mem_sInter.mpr xs) _ ts) ((Set.mem_sInter.mpr ys) _ ts) hs ht h1

theorem convex_inter {s t : Set M} (hs : Convex R s) (ht : Convex R t) : Convex R (s ∩ t) := by
  simpa using convex_sInter (S := {s,t}) (by simpa using ⟨hs, ht⟩)

variable (R) in
/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convexHull : ClosureOperator (Set M) := .ofCompletePred (Convex R) fun _ ↦ convex_sInter

variable (R M) in
theorem empty_convex : Convex R (∅ : Set M) := by simp [Convex]

theorem convexHull_convex {s : Set M} : Convex R (convexHull R s) := by
  unfold Convex
  simp only [convexHull, ClosureOperator.ofCompletePred_apply, Set.le_eq_subset, Set.iInf_eq_iInter,
    Set.mem_iInter, Subtype.forall, and_imp]
  intro x hx y hy a b ha hb h w hw ht
  exact (ht (hx w hw ht) (hy w hw ht) ha hb h)

variable (R) in
/-- Open segment in a vector space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def openSegment (x y : M) : Set M :=
  { z : M | ∃ (a b : R) (a0 : 0 < a) (b0 : 0 < b) (ab : a + b = 1),
    convexComboPair a b a0.le b0.le ab x y = z }

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

theorem isExtreme_empty {S : Set M} : IsExtreme R S ∅ where
  subset := S.empty_subset
  left_mem_of_mem_openSegment := by simp

variable (R M) in
structure ConvexSet where
  carrier : Set M
  convex : ConvexSpace.Convex R carrier

namespace ConvexSet

instance : SetLike (ConvexSet R M) M where
  coe F := F.carrier
  coe_injective' := by sorry

instance : PartialOrder (ConvexSet R M) := .ofSetLike _ M

@[simp]
theorem coe_carrier {F : ConvexSet R M} : SetLike.coe F = F.carrier := by rfl

instance : OrderBot (ConvexSet R M) where
  bot := ⟨∅, empty_convex R M⟩
  bot_le _ := Set.subset_iff_notMem.mpr fun ⦃_⦄ _ a ↦ a

@[ext]
theorem ext {F₁ F₂ : ConvexSet R M} (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

def IsFaceOf (F C : ConvexSet R M) := IsExtreme R C F.carrier

/-- A face of a convex set `P`. Represents the face lattice of `P`. -/
structure Face (P : ConvexSet R M) extends toConvexSet : ConvexSet R M where
  isFaceOf : IsFaceOf toConvexSet P

variable {P : ConvexSet R M}

instance : SetLike (Face P) M where
  coe F := F.toConvexSet
  coe_injective' := by sorry

instance : PartialOrder (Face P) := .ofSetLike (Face P) M

instance : Bot (Face P) := ⟨⟨∅, ConvexSpace.empty_convex R M⟩, sorry⟩

end ConvexSet

end ConvexSpace

end Convex
