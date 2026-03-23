module

public import Mathlib.LinearAlgebra.ConvexSpace

public import Mathlib.Tactic

/-!
# Affine space

-/

public section

noncomputable section

/--
A finitely supported weighting over elements of `M` with coefficients in `R`. The weights sum to 1.
-/
structure AffineWeights (R : Type*) [AddCommMonoid R] [One R] (M : Type*)
    extends weights : M →₀ R where
  /-- The weights sum to 1. -/
  total : weights.sum (fun _ r => r) = 1

attribute [simp] AffineWeights.total
grind_pattern AffineWeights.total => self.weights

namespace AffineWeights

variable {R : Type*} [AddCommMonoid R] [One R] {M : Type*}

@[ext]
theorem ext {f g : AffineWeights R M} (h : f.weights = g.weights) : f = g := by
  cases f; cases g; simp_all

/-- The weighting that puts all weight on `x`. -/
def single (x : M) : AffineWeights R M where
  weights := Finsupp.single x 1
  total := by simp

@[simp]
theorem mk_single (x : M) {total} :
    (AffineWeights.mk (Finsupp.single x (1 : R)) total) = single x := by simp [single]

/-- A weighting with weight `s` on `x` and weight `t` on `y`. -/
def duple (x y : M) {s t : R} (h : s + t = 1) : AffineWeights R M where
  weights := Finsupp.single x s + Finsupp.single y t
  total := by
    classical
    rw [Finsupp.sum_add_index] <;> simp [h]

/--
Map a function over the support of an affine weighting.
For each n : N, the weight is the sum of weights of all m : M with g m = n.
-/
def map {M : Type*} {N : Type*} (g : M → N) (f : AffineWeights R M) : AffineWeights R N where
  weights := f.weights.mapDomain g
  total := by simp [Finsupp.sum_mapDomain_index]

@[simp]
lemma map_map {M N O : Type*} (f : M → N) (g : N → O) (p : AffineWeights R M) :
    (map g (map f p)) = (map (g ∘ f) p) := by
  simp [map, Finsupp.mapDomain, Finsupp.sum_sum_index, Finsupp.sum_single_index]

/--
Join operation for affine weightings (monadic join).
Given a weighting of a weighting, flattens it to a single weighting.
-/
def join {R : Type*} [Semiring R] {M : Type*} (f : AffineWeights R (AffineWeights R M)) :
    AffineWeights R M where
  weights := f.weights.sum (fun d r => r • d.weights)
  total := by
    rw [Finsupp.sum_sum_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
    convert f.total
    rw [Finsupp.sum_smul_index (fun _ ↦ rfl), ← Finsupp.mul_sum, AffineWeights.total, mul_one]

-- instance AffineMonad : Monad (AffineWeights R) where
--   pure := AffineWeights.single
--   bind w f := (w.map f).join

end AffineWeights

/--
A set equipped with an operation of finite affine combinations, where the coefficients sum to 1.
-/
class AffineSpace (R : Type*) (M : Type*) [Semiring R] where
  /-- Take a affine combination with the given weighting. -/
  affineCombination (f : AffineWeights R M) : M
  /-- Associativity of affine combination (monadic join law). -/
  assoc (f : AffineWeights R (AffineWeights R M)) :
    affineCombination (f.map affineCombination) = affineCombination f.join
  /-- A affine combination of a single point is that point. -/
  single (x : M) : affineCombination (.single x) = x

namespace AffineSpace

section ConvexSpace

variable {R : Type*} {M : Type*} [LE R] [Semiring R] in
-- its probably nicer to redefine StdSimplex to extend AffineWeights?
instance : Coe (StdSimplex R M) (AffineWeights R M) where
  coe f := ⟨f.weights, f.total⟩

variable {R : Type*} {M : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

instance : Coe (StdSimplex R (StdSimplex R M)) (AffineWeights R (AffineWeights R M)) where
  coe f := f.map (Coe.coe (β := (AffineWeights R M)))

/-- An affine space is a convex space too. -/
instance [af : AffineSpace R M] : ConvexSpace R M where
  convexCombination (f : StdSimplex R M) := af.affineCombination f
  assoc (f : StdSimplex R (StdSimplex R M)) := by
    convert af.assoc f
    · simp only [StdSimplex.map, AffineWeights.map, ← Finsupp.mapDomain_comp]; rfl
    · simp only [StdSimplex.join, AffineWeights.join, StdSimplex.map]
      rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]
  single (x : M) := by convert af.single x

end ConvexSpace

section Convex

variable (R : Type*) {M : Type*}
variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [AffineSpace R M]

/-- Convexity of sets in affine spaces. -/
def Convex (s : Set M) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : R⦄ (hs : 0 ≤ a) (ht : 0 ≤ b) (h : a + b = 1),
    (convexComboPair a b hs ht h x y) ∈ s

theorem convex_sInter {S : Set (Set M)} (h : ∀ s ∈ S, Convex R s) : Convex R (⋂₀ S) :=
  fun _ xs _ ys _ _ hs ht h1 t ts =>
    h t ts ((Set.mem_sInter.mpr xs) _ ts) ((Set.mem_sInter.mpr ys) _ ts) hs ht h1

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convexHull : ClosureOperator (Set M) := .ofCompletePred (Convex R) fun _ ↦ convex_sInter R

end Convex

section IsExtreme

section OpenSegment

open AffineWeights

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜] [AffineSpace 𝕜 E]
variable (𝕜)

/-- Open segment in an affine space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def openSegment (x y : E) : Set E :=
  { z : E | ∃ s t : 𝕜, 0 < s ∧ 0 < t ∧ ∃ h : s + t = 1, z = affineCombination (duple x y h)}

theorem openSegment_symm (x y : E) : openSegment 𝕜 x y = openSegment 𝕜 y x :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, by simp [H, duple, add_comm]⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab,  by simp [H, duple, add_comm]⟩⟩

end OpenSegment

variable (R : Type*) {M : Type*} [Semiring R] [AffineSpace R M] [PartialOrder R]

/-- A set `B` is an extreme subset of `A` if `B ⊆ A` and all points of `B` only belong to open
segments whose ends are in `B`.

Our definition only requires that the left endpoint of the segment lies in `B`,
but by symmetry of open segments, the right endpoint must also lie in `B`. -/
@[mk_iff]
structure IsExtreme (A B : Set M) : Prop where
  subset : B ⊆ A
  left_mem_of_mem_openSegment : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A →
    ∀ ⦃z⦄, z ∈ B → z ∈ openSegment R x y → x ∈ B

-- some sanity checks

@[refl]
protected theorem IsExtreme.refl (A : Set M) : IsExtreme R A A :=
  ⟨Set.Subset.refl A, fun _ hx₁A _ _ _ _ _ ↦ hx₁A⟩

variable {R} {A B C : Set M} {x : M}

theorem IsExtreme.right_mem_of_mem_openSegment (h : IsExtreme R A B) {y z : M} (hx : x ∈ A)
    (hy : y ∈ A) (hz : z ∈ B) (hzxy : z ∈ openSegment R x y) : y ∈ B :=
  h.left_mem_of_mem_openSegment hy hx hz <| by rwa [openSegment_symm]

@[trans]
protected theorem IsExtreme.trans (hAB : IsExtreme R A B) (hBC : IsExtreme R B C) :
    IsExtreme R A C := by
  refine ⟨hBC.subset.trans hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxC hx ↦ ?_⟩
  exact hBC.left_mem_of_mem_openSegment
    (hAB.left_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx)
    (hAB.right_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx) hxC hx

protected theorem IsExtreme.antisymm : Std.Antisymm (IsExtreme R : Set M → Set M → Prop) :=
  ⟨fun _ _ hAB hBA ↦ Set.Subset.antisymm hBA.1 hAB.1⟩

instance : IsPartialOrder (Set M) (IsExtreme R) where
  refl := IsExtreme.refl R
  trans _ _ _ := IsExtreme.trans
  antisymm := IsExtreme.antisymm.antisymm

end IsExtreme

end AffineSpace

noncomputable section AddTorsor

namespace AddTorsor

variable {R : Type*} {V : Type*} {P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- The affine combination of points in an AddTorsor. -/
public def affineCombination (s : AffineWeights R P) : P :=
  s.weights.support.affineCombination R id s.weights

variable [PartialOrder R] [IsStrictOrderedRing R] in
public theorem affineCombination_single (x : P) :
    affineCombination (AffineWeights.single (R := R) x) = x := by
  simp only [affineCombination, AffineWeights.single]
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  refine ({x} : Finset P).affineCombination_of_eq_one_of_eq_zero _ _
    (Finset.mem_singleton_self x) (by simp) fun j _ hne => Finsupp.single_eq_of_ne hne

variable [IsCancelMulZero R] in
public theorem affineCombination_assoc (f : AffineWeights R (AffineWeights R P)) :
    affineCombination (f.map affineCombination) = affineCombination f.join := by
  classical
  -- Choose a base point
  obtain ⟨b⟩ : Nonempty P := inferInstance
  -- Express both sides using weightedVSubOfPoint with base point b
  have hL := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (f.map affineCombination).weights.support (f.map affineCombination).weights id
    (f.map affineCombination).total b
  have hR := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    f.join.weights.support f.join.weights id f.join.total b
  simp only [affineCombination, hL, hR]
  congr 1
  -- Now show the weighted vector sums are equal
  simp only [Finset.weightedVSubOfPoint_apply, AffineWeights.map, AffineWeights.join, id]
  -- Rewrite LHS using sum_mapDomain_index
  change (Finsupp.mapDomain affineCombination f.weights).sum (fun x w => w • (x -ᵥ b)) = _
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
  simp only [Finsupp.sum, affineCombination]
  -- Expand affineCombination d using base point b
  conv_lhs =>
    congr; · skip
    ext d
    rw [d.weights.support.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
        _ _ d.total b, vadd_vsub, Finset.weightedVSubOfPoint_apply]
    simp only [id]
  simp_rw [Finset.smul_sum, smul_smul]
  -- Expand RHS using sum_finset_sum_index
  let h : P → R → V := fun x w => w • (x -ᵥ b)
  have h_rhs : (∑ d ∈ f.weights.support, f.weights d • d.weights).sum h
      = ∑ d ∈ f.weights.support, (f.weights d • d.weights).sum h :=
    (Finsupp.sum_finset_sum_index (h := h) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)).symm
  simp only [Finsupp.sum] at h_rhs ⊢
  rw [h_rhs]
  -- Both sides are now double sums; show the inner sums match
  congr 1
  ext d
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- Show that d.support = (f.weights d • d.weights).support
  by_cases hd : f.weights d = 0
  · simp [hd]
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finsupp.mem_support_iff, ne_eq]
    constructor
    · exact fun hp => smul_ne_zero hd hp
    · intro hp hp'
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hp', mul_zero,
        not_true_eq_false] at hp

variable [PartialOrder R] [IsStrictOrderedRing R] [IsCancelMulZero R]
/-- An AddTorsor is also an AffineSpace. -/
public instance instAffineSpace : AffineSpace R P where
  affineCombination f := affineCombination f
  single := affineCombination_single
  assoc := affineCombination_assoc

end AddTorsor
