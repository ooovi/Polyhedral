import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Lattice
import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace

section Semiring

-- Eventually, most of the below will become global names
namespace Convexity

variable {R : Type*} {M : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M]

-- the following is copied from the mathlib convexity def and adapted to ours

variable (R) in
/-- Open segment in a convex space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def openSegment (x y : M) : Set M :=
  { z : M | ∃ (a b : R) (a0 : 0 < a) (b0 : 0 < b) (ab : a + b = 1),
    convexCombPair a b a0.le b0.le ab x y = z }

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

namespace ConvexSet

def IsFaceOf (F C : ConvexSet R M) := IsExtreme R C (F : Set M)

/-- A face of a convex set `P`. Represents the face lattice of `P`. -/
structure Face (P : ConvexSet R M) extends toConvexSet : ConvexSet R M where
  isFaceOf : IsFaceOf toConvexSet P

namespace Face

variable {P : ConvexSet R M}

instance : SetLike (Face P) M where
  coe F := F.toConvexSet.carrier
  coe_injective' a b _ := sorry

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

section Ring

variable {R A : Type*}
variable [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [AddTorsor V A]

namespace Convexity.ConvexSet.Face

variable {C : ConvexSet R A}

noncomputable abbrev rank (F : C.Face) : Cardinal := F.toConvexSet.rank

noncomputable abbrev finrank (F : C.Face) : ℕ := F.toConvexSet.finrank

end Convexity.ConvexSet.Face

end Ring
