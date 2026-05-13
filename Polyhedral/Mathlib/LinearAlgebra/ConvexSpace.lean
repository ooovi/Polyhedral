import Mathlib.LinearAlgebra.ConvexSpace.AffineSpace
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

section Semiring

-- Eventually, most of the below will become global names
namespace ConvexSpace

variable {R : Type*} {M : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M]

-- we redefine what we need using `ConvexSpace`.

variable (R) in
/-- A set is convex if it contains all convex combinations of any two of its points. -/
def IsConvex (s : Set M) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : R⦄ (hs : 0 ≤ a) (ht : 0 ≤ b) (h : a + b = 1),
    convexComboPair a b hs ht h x y ∈ s

theorem isConvex_sInter {S : Set (Set M)} (h : ∀ s ∈ S, IsConvex R s) : IsConvex R (⋂₀ S) :=
  fun _ xs _ ys _ _ hs ht h1 t ts =>
    h t ts ((Set.mem_sInter.mpr xs) _ ts) ((Set.mem_sInter.mpr ys) _ ts) hs ht h1

theorem isConvex_inter {s t : Set M} (hs : IsConvex R s) (ht : IsConvex R t) : IsConvex R (s ∩ t) := by
  simpa using isConvex_sInter (S := {s,t}) (by simpa using ⟨hs, ht⟩)

variable (R) in
/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convexHull : ClosureOperator (Set M) := .ofCompletePred (IsConvex R) fun _ ↦ isConvex_sInter

theorem isConvex_empty : IsConvex R (M := M) ∅ := by
  intro x hx y hy a b ha hb h
  simp only [Set.mem_empty_iff_false]
  contradiction

theorem isConvex_univ : IsConvex R (Set.univ : Set M) := by simp [IsConvex]

theorem isConvex_convexHull {s : Set M} : IsConvex R (convexHull R s) := by
  unfold IsConvex
  simp only [convexHull, ClosureOperator.ofCompletePred_apply, Set.le_eq_subset, Set.iInf_eq_iInter,
    Set.mem_iInter, Subtype.forall, and_imp]
  intro x hx y hy a b ha hb h w hw ht
  exact (ht (hx w hw ht) (hy w hw ht) ha hb h)

theorem convexHull_min {s t : Set M} (hs : s ⊆ t) (hc : IsConvex R t) : convexHull R s ⊆ t :=
  Set.iInter_subset (fun (b : { b // s ⊆ b ∧ IsConvex R b }) => (b : Set M)) ⟨t, ⟨hs, hc⟩⟩

-- the following is copied from the mathlib convexity def and adapted to ours

variable (R) in
/-- Open segment in a convex space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when
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

-- these correspond to our pointed cones, so we define the face lattice

variable (R M) in
structure ConvexSet where
  carrier : Set M
  convex : ConvexSpace.IsConvex R carrier

namespace ConvexSet

instance : SetLike (ConvexSet R M) M where
  coe F := F.carrier
  coe_injective' K₁ K₂ _ := by cases K₁; cases K₂; congr

@[simp] theorem carrier_eq_coe {P : ConvexSet R M} : P.carrier = P := by rfl

@[simp] theorem mem_coe {P : ConvexSet R M} (x : M) : x ∈ P.carrier ↔ x ∈ P := .rfl

@[ext] theorem ext {F₁ F₂ : ConvexSet R M} (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : ConvexSet R M) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : ConvexSet R M) = s := by ext; simp

instance : PartialOrder (ConvexSet R M) := .ofSetLike ..

instance : OrderBot (ConvexSet R M) where
  bot := ⟨∅, isConvex_empty⟩
  bot_le _ := Set.subset_iff_notMem.mpr fun ⦃_⦄ _ a ↦ a

@[simp] lemma not_mem_bot (x : M) : x ∉ (⊥ : ConvexSet R M) := by
  change x ∉ (∅ : Set M); simp

def convexHull (s : Set M) : ConvexSet R M := ⟨_, isConvex_convexHull (s := s)⟩

def IsFaceOf (F C : ConvexSet R M) := IsExtreme R C (F : Set M)

/-- A face of a convex set `P`. Represents the face lattice of `P`. -/
structure Face (P : ConvexSet R M) extends toConvexSet : ConvexSet R M where
  isFaceOf : IsFaceOf toConvexSet P

namespace Face

variable {P : ConvexSet R M}

instance : SetLike (Face P) M where
  coe F := F.toConvexSet
  coe_injective' := sorry

@[simp] theorem carrier_eq_coe {F : Face P} : F.carrier = F := by rfl

@[simp] theorem mem_coe {F : Face P} (x : M) : x ∈ F.carrier ↔ x ∈ F := .rfl

@[ext] theorem ext {F₁ F₂ : Face P} (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

instance : PartialOrder (Face P) := .ofSetLike ..

instance : Bot (Face P) :=
  ⟨⟨∅, isConvex_empty⟩, by simp [IsFaceOf, ← ConvexSet.carrier_eq_coe, isExtreme_empty]⟩

lemma nonempty_of_ne_bot {F : Face P} (h : F ≠ ⊥) : (F : Set M).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro heq
  apply h
  ext
  simp [← SetLike.mem_coe, heq, Bot.bot]
  sorry

end Face

end ConvexSet

end ConvexSpace

end Semiring

section Ring

variable {R M P : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
   [Module R M]

lemma convexComboPair_eq_smul_add_smul {x y a b} (a0 : (0 : R) ≤ a) (b0 : (0 : R) ≤ b)
      (ab : a + b = 1) :
    convexComboPair (M := M) a b a0 b0 ab x y = a • x + b • y := by
  classical
  simp only [convexComboPair, convexCombination_eq_sum (StdSimplex.duple x y a0 b0 ab)]
  unfold StdSimplex.duple
  rw [Finsupp.sum_add_index]
  · simp [Finsupp.sum_single_index]
  · exact (fun i j => zero_smul _ _)
  · simp [add_smul]

namespace ConvexSpace

-- for now, a way to translate from our convexity to mathlib convexity in case of a vector space.
-- eventually, these should be proven directly...

/-- In a vector space, convexity is equivalent to star-convexity at all points. -/
private theorem convex_iff_StarConvex (s : Set M) :
    ConvexSpace.IsConvex R s ↔ ∀ ⦃x : M⦄, x ∈ s → StarConvex R x s := by
  simp [ConvexSpace.IsConvex, StarConvex, convexComboPair_eq_smul_add_smul]

theorem submodule_convex (S : Submodule R M) : ConvexSpace.IsConvex R (S : Set M) := by
  rw [convex_iff_StarConvex]
  exact S.convex

theorem pointedCone_convex (P : PointedCone R M) : ConvexSpace.IsConvex R (P : Set M) := by
  rw [convex_iff_StarConvex]
  exact P.convex

variable (R) in
theorem Submodule.span_convexHull_eq_span (t : Set M) :
    Submodule.span R t = Submodule.span R (ConvexSpace.convexHull R t) := by
  ext x; constructor <;> intro h
  · exact Submodule.span_mono (by simpa [ConvexSpace.convexHull] using fun _ a _ ↦ a) h
  apply Submodule.mem_span.mp h
  simp only [ConvexSpace.convexHull, ClosureOperator.ofCompletePred_apply, Set.le_eq_subset,
    Set.iInf_eq_iInter]
  intro a am
  simp only [Set.mem_iInter, Subtype.forall, and_imp, SetLike.mem_coe, Submodule.mem_span] at ⊢ am
  exact fun p hp ↦ am _ hp <| submodule_convex p

open PointedCone in
variable (R) in
theorem PointedCone.hull_convexHull_eq_hull (t : Set M) :
    hull R t = hull R (ConvexSpace.convexHull R t) := by
  ext x; constructor <;> intro h
  · exact Submodule.span_mono (by simpa [ConvexSpace.convexHull] using fun _ a _ ↦ a) h
  apply Submodule.mem_span.mp h
  simp only [ConvexSpace.convexHull, ClosureOperator.ofCompletePred_apply, Set.le_eq_subset,
    Set.iInf_eq_iInter]
  intro a am
  simp only [Set.mem_iInter, Subtype.forall, and_imp, SetLike.mem_coe, Submodule.mem_span] at ⊢ am
  exact fun p hp ↦ am _ hp <| pointedCone_convex p

end ConvexSpace

end Ring

section Field

variable {R M P : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
   [Module R M]

open PointedCone Set Pointwise

namespace ConvexSpace

-- yaël realized the following three don't hold over non-fields
theorem convexCombination_mem_convexHull {s} (w : StdSimplex R M) (h : IsConvex R s) :
    letI : ConvexSpace R M := AddTorsor.instConvexSpace
    convexCombination w ∈ s := by
  sorry
  -- this needs a way to split convexCombination into convexComboPair.

theorem Finset.convexHull_eq (s : Finset M) : convexHull R ↑s =
    letI : ConvexSpace R M := AddTorsor.instConvexSpace
    { x : M | ∃ (w : StdSimplex R M), convexCombination w = x } := by
  classical
  refine Set.Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    rw [Finset.mem_coe] at hx
    use StdSimplex.single x
    simp
  · intro _
    simp [convexComboPair]
  · rintro x hx a ⟨⟨aa, ⟨aale, ha⟩⟩, rfl⟩
    obtain ⟨w, rfl⟩ := hx
    exact convexCombination_mem_convexHull w ha

theorem Finset.mem_convexHull {s : Finset M} {x : M} :
    letI : ConvexSpace R M := AddTorsor.instConvexSpace
    x ∈ convexHull R s ↔ ∃ (w : StdSimplex R M), convexCombination w = x := by
  simp [Finset.convexHull_eq]

variable {s : Set M}

-- the following two lemmas exist for mathlib convexity but we need them for our convexity :(

/-- The cone hull of a convex set is the union of the closed halflines through that set. -/
lemma mem_hull_iff_of_convex' (hs : s.Nonempty) (hc : ConvexSpace.IsConvex R s) (x : M) :
    x ∈ hull R s ↔ x ∈ Ici (0 : R) • s := by
  rw [convex_iff_StarConvex] at hc
  exact mem_hull_iff_of_convex (R := R) hs hc x

/-- Every nonzero member of the conic hull of a convex set is a pos. smultiple of a set member. -/
theorem mem_hull_iff_mem_pos_smul_of_convex_nonzero' {x : M} {s} (hc : ConvexSpace.IsConvex R s)
    (hx : x ≠ 0) :
    x ∈ hull R s ↔ x ∈ Ioi (0 : R) • s := by
  by_cases hs : s.Nonempty
  · constructor <;> intro h
    · obtain ⟨r, rpos, hr⟩ := (mem_hull_iff_of_convex' hs hc _).mp h
      rcases eq_or_ne 0 r with rfl | h
      · simp_all
      exact ⟨r, lt_of_le_of_ne rpos h, hr⟩
    · simp [mem_hull_iff_of_convex' hs hc, Set.smul_subset_smul_right Ioi_subset_Ici_self h]
  · simp [Set.not_nonempty_iff_eq_empty.mp hs, hx]

end ConvexSpace

end Field
