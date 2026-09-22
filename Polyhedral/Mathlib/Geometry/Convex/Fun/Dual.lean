/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Module
public import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.WithTop
public import Polyhedral.Mathlib.Geometry.Convex.Fun.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The dual of a convex function

Given a bilinear pairing `p` between two `R`-modules `M` and `N`, we define the *dual*, aka *convex
conjugate*, aka *Legendre–Fenchel transform*, of a function `f : M → WithBot (WithTop R)` to be the
function `Convexity.dual p f : N → WithBot (WithTop R)` given by `dual p f y = ⨆ x, p x y - f x`.

The dual of a function is always convex, and the bidual of a function is the largest convex function
below it (at least in nice enough situations). This makes duality the main tool to reduce statements
about convex functions to statements about affine functions.

## Main declarations

* `Convexity.dual`: The dual of a function along a bilinear pairing.
* `Convexity.le_add_dual`: **Fenchel–Young inequality**.
* `Convexity.isConvexFunOn_dual`: The dual of a function is convex.
* `Convexity.dual_dual_le`: The bidual of a function is at most that function.

## Implementation notes

Extended scalars do not carry a subtraction (there is no good value for `⊤ - ⊤`), so we cannot
literally write `dual p f y = ⨆ x, p x y - f x`. Instead, we take the supremum of `p x y - r` over
the *epigraph* of `f`, namely over all pairs `(x, r) : M × R` with `f x ≤ r`. This yields the same
function, since the supremum of `p x y - r` over `r ≥ f x` is `p x y - f x`, with the expected
conventions when `f x = ⊤` (there is no such `r`, so `x` contributes nothing) and when `f x = ⊥`
(every `r` works, so `x` contributes `⊤`).

Note that this mirrors the epigraph-based definition of `Convexity.IsConvexFunOn`.

Taking suprema forces the scalars to be conditionally complete, which is why we assume
`[ConditionallyCompleteLinearOrder R]` throughout.
-/

open Set

public noncomputable section

namespace Convexity
variable {R M N : Type*} [Field R] [ConditionallyCompleteLinearOrder R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R} {f g : M → WithBot (WithTop R)} {z : WithBot (WithTop R)} {x : M} {y : N}
  {r : R}

local notation3 "R∞" => WithBot (WithTop R)

omit [Field R] [ConditionallyCompleteLinearOrder R] in
private lemma exists_eq_coe (z : R∞) : z = ⊥ ∨ z = ⊤ ∨ ∃ s : R, z = (s : R∞) :=
  match z with
  | ⊥ => .inl rfl
  | (⊤ : WithTop R) => .inr (.inl rfl)
  | ((s : R) : WithTop R) => .inr (.inr ⟨s, rfl⟩)

variable (p f) in
/-- The dual, aka convex conjugate, of a function `f : M → R∞` along a bilinear pairing
`p : M →ₗ[R] N →ₗ[R] R`, namely `dual p f y = ⨆ x, p x y - f x`.

To avoid subtracting extended scalars, we phrase this as the supremum of `p x y - r` over the
epigraph `{(x, r) | f x ≤ r}` of `f`. -/
def dual (y : N) : R∞ := ⨆ (x : M) (r : R) (_ : f x ≤ (r : R∞)), ((p x y - r : R) : R∞)

/-- The defining property of the dual: `p x y - r` is at most `dual p f y` whenever `(x, r)` lies in
the epigraph of `f`. -/
lemma le_dual (hxr : f x ≤ (r : R∞)) : ((p x y - r : R) : R∞) ≤ dual p f y :=
  le_iSup_of_le x <| le_iSup_of_le r <| le_iSup_of_le hxr le_rfl

lemma dual_le_iff :
    dual p f y ≤ z ↔ ∀ x, ∀ r : R, f x ≤ (r : R∞) → ((p x y - r : R) : R∞) ≤ z := by
  simp [dual]

@[gcongr]
lemma dual_le_dual (hfg : f ≤ g) (y : N) : dual p g y ≤ dual p f y :=
  dual_le_iff.2 fun x _r hxr ↦ le_dual <| (hfg x).trans hxr

lemma dual_antitone : Antitone (dual p) := fun _f _g hfg _y ↦ dual_le_dual hfg _

@[simp] lemma dual_top : dual p (⊤ : M → R∞) = ⊥ := by ext y; simp [dual]

section IsStrictOrderedRing
variable [IsStrictOrderedRing R]

@[simp] lemma dual_bot [Nonempty M] : dual p (⊥ : M → R∞) = ⊤ := by
  ext y
  obtain ⟨x⟩ := ‹Nonempty M›
  have key (r : R) : ((p x y - r : R) : R∞) ≤ dual p ⊥ y := le_dual (by simp)
  obtain h | h | ⟨s, h⟩ := exists_eq_coe (dual p (⊥ : M → R∞) y)
  · rw [h] at key; simpa using key 0
  · exact h
  · rw [h] at key
    have := key (p x y - (s + 1))
    rw [sub_sub_cancel] at this
    exact absurd (by exact_mod_cast this : s + 1 ≤ s) (by simp)

/-- **Fenchel–Young inequality**: `p x y ≤ f x + dual p f y`, in the form avoiding the addition of
infinities. -/
theorem le_add_dual (hxr : f x ≤ (r : R∞)) (y : N) :
    ((p x y : R) : R∞) ≤ (r : R∞) + dual p f y :=
  calc ((p x y : R) : R∞) = ((r + (p x y - r) : R) : R∞) := by rw [add_sub_cancel]
    _ = (r : R∞) + ((p x y - r : R) : R∞) := by norm_cast
    _ ≤ (r : R∞) + dual p f y := by gcongr; exact le_dual hxr

/-! ### The bidual -/

variable (p f) in
/-- The bidual of a function is at most that function. -/
theorem dual_dual_le : dual p.flip (dual p f) ≤ f := fun x ↦ by
  rw [dual_le_iff]
  rintro y r hyr
  rw [LinearMap.flip_apply]
  obtain hfx | hfx | ⟨s, hfx⟩ := exists_eq_coe (f x)
  · -- `f x = ⊥` forces `dual p f y = ⊤`, contradicting `dual p f y ≤ r`.
    exfalso
    have key (t : R) : p x y - t ≤ r := by
      exact_mod_cast (le_dual (f := f) (x := x) (r := t) (y := y) (by simp [hfx])).trans hyr
    have := key (p x y - (r + 1))
    rw [sub_sub_cancel] at this
    exact absurd this (by simp)
  · simp [hfx]
  · have hle : ((p x y - s : R) : R∞) ≤ (r : R∞) := (le_dual (by simp [hfx])).trans hyr
    rw [hfx]
    exact_mod_cast sub_le_comm.1 (by exact_mod_cast hle)

end IsStrictOrderedRing

/-! ### Convexity of the dual -/

section ConvexSpace
variable [IsStrictOrderedRing R] [ConvexSpace R N] [IsModuleConvexSpace R N]

private lemma isAffineMap_sub_const (p : M →ₗ[R] N →ₗ[R] R) (x : M) (r : R) :
    IsAffineMap R fun y : N ↦ ((p x y - r : R) : R∞) :=
  (isAffineMap_withBotSome.comp isAffineMap_withTopSome).comp
    ((IsAffineMap.linearMap (p x)).sub (.const r))

/-- The dual of a function is convex, being a supremum of affine functions. -/
theorem isConvexFunOn_dual : IsConvexFunOn R univ (dual p f) := by
  refine .of_isConvexSet_epigraph ?_
  have : {(y, z) : N × R∞ | y ∈ univ ∧ dual p f y ≤ z}
      = ⋂ (x : M) (r : R) (_ : f x ≤ (r : R∞)),
          {(y, z) : N × R∞ | y ∈ univ ∧ ((p x y - r : R) : R∞) ≤ z} := by
    ext ⟨y, z⟩; simp [dual_le_iff]
  rw [this]
  exact .iInter fun x ↦ .iInter fun r ↦ .iInter fun _ ↦
    (IsAffineMap.isConvexFunOn .univ (isAffineMap_sub_const p x r)).isConvexSet_epigraph

end ConvexSpace

end Convexity
