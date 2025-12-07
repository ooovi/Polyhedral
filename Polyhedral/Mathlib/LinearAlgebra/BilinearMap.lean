/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Polyhedral.Mathlib.LinearAlgebra.Dual.Basis

open Module Function

namespace LinearMap

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

-- variable (p) in
-- lemma exists_restricted_pairing (S : Submodule R M) :
--     ∃ T : Submodule R N, ∃ q : S →ₗ[R] T →ₗ[R] R, ∀ s : S, ∀ t : T, q s t = p s t := by
--   sorry

end CommSemiring

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]

-- def Radical (p : M →ₗ[R] N →ₗ[R] R) := ker p.flip
-- def Radical' (p : M →ₗ[R] N →ₗ[R] R) := ker p

-- def IsSeparating (p : M →ₗ[R] N →ₗ[R] R)
--     := ∀ x : M, p x = 0 → x = 0

-- alias IsSeparating := SeparatingLeft

/- For a field this is known as being 'formally real'. This is equivalent to the existence of an
  ordered field structure. This could be relevant on field with no preferred order, e.g. the
  field of rational functions -/
def IsFaithfulPair (p : M →ₗ[R] N →ₗ[R] R)
    := ∃ g : N →ₗ[R] M, ∀ x : N, (p ∘ₗ g) x x = 0 → x = 0 -- equiv: (p x) (g x) = 0 → x = 0

/- If p is faithful then there is an embedding of N in M on which p is injective.
  In prticular, N is "smaller" than M. So Dual.eval is not faithful for infinite spaces, while
  .id is always faithful.
  This is intentionally weaker than a perfect pairing. In this way one direction of the standard
  duality map can still be faithful, even in infinite dimensions.
  This allows to, e.g. consider duality between M and its continuous dual.
-/

variable {p : M →ₗ[R] N →ₗ[R] R}

-- lemma funext_zero {α : Type*} {β : Type*} {f : Type*} [Zero α] [Zero β] [FunLike f α β]
--     (hf : ∀ x, f x = 0) : f = 0 := funext hf
-- lemma funext_zero {α : Type*} {β : Type*} [Zero α] [Zero β] {f : α → β}
--     (hf : ∀ x, f x = 0) : f = 0 := funext hf
-- lemma funext_zero_iff {α : Type*} {β : Type*} [Zero α] [Zero β] (f : α → β) :
--     f = 0 ↔ ∀ x, f x = 0 := funext_iff

-- ## SeparatingLeft

-- lemma SeparatingLeft.iff_zero_of_forall_zero : p.SeparatingLeft ↔ ∀ x, p x = 0 → x = 0 where
--   mp h x hx := by simpa [hx] using h x
--   mpr h x hx := h x (ext hx)
-- lemma SeparatingLeft.zero_of_forall_zero (hp : p.SeparatingLeft) :
--     ∀ x, p x = 0 → x = 0 := iff_zero_of_forall_zero.mp hp

-- lemma SeparatingLeft.iff_ker_eq_bot : p.SeparatingLeft ↔ ker p = ⊥ := by
--   simpa only [iff_zero_of_forall_zero] using ker_eq_bot'.symm
-- lemma SeparatingLeft.ker_eq_bot (hp : p.SeparatingLeft) : ker p = ⊥ := iff_ker_eq_bot.mp hp

lemma SeparatingLeft.of_injective (hp : Injective p) : p.SeparatingLeft := by
  simpa [separatingLeft_iff_ker_eq_bot] using ker_eq_bot_of_injective hp
instance [inst : Fact (Injective p)] : Fact p.SeparatingLeft :=
    ⟨SeparatingLeft.of_injective inst.elim⟩

-- instance [inst : Fact p.SeparatingLeft] : Fact p.flip.flip.SeparatingLeft := inst

lemma SeparatingLeft.flip_of_isFaithfulPair (hp : p.IsFaithfulPair) : p.SeparatingRight := by
  obtain ⟨g, hg⟩ := hp
  intro x hx
  simpa [hx] using hg x

instance [inst : Fact p.IsFaithfulPair] : Fact p.SeparatingRight :=
    ⟨SeparatingLeft.flip_of_isFaithfulPair inst.elim⟩
instance [inst : Fact p.flip.IsFaithfulPair] : Fact p.SeparatingLeft :=
    ⟨SeparatingLeft.flip_of_isFaithfulPair inst.elim⟩


variable [Module.Projective R N] in
instance : Fact (.id : (N →ₗ[R] R) →ₗ[R] (N →ₗ[R] R)).SeparatingRight :=
    ⟨fun x hx => by simpa using (forall_dual_apply_eq_zero_iff R x).mp hx⟩

variable [Module.Projective R M] in
instance : Fact (Dual.eval R M).SeparatingLeft :=
    ⟨by simp [separatingLeft_iff_linear_nontrivial, eval_apply_eq_zero_iff]⟩

instance : Fact (.id : (N →ₗ[R] R) →ₗ[R] (N →ₗ[R] R)).SeparatingLeft :=
    ⟨fun x hx => by ext y; exact hx y⟩

instance : Fact (Dual.eval R M).SeparatingRight :=
    ⟨by simp [Dual.eval, separatingLeft_iff_linear_nontrivial]⟩


-- instance [inst : Fact p.flip.SeparatingLeft] : Fact p.SeparatingRight :=
--     ⟨flip_separatingLeft.mp inst.elim⟩
-- instance [inst : Fact p.flip.SeparatingRight] : Fact p.SeparatingLeft :=
--     ⟨flip_separatingRight.mp inst.elim⟩

instance [inst : Fact p.SeparatingLeft] : Fact p.flip.SeparatingRight :=
    ⟨flip_separatingLeft.mp inst.elim⟩
instance [inst : Fact p.SeparatingRight] : Fact p.flip.SeparatingLeft :=
    ⟨flip_separatingRight.mp inst.elim⟩

instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingLeft := ⟨inst.elim.1⟩
instance [inst : Fact p.Nondegenerate] : Fact p.SeparatingRight := ⟨inst.elim.2⟩

variable [inst : Fact p.SeparatingLeft] in
@[simp] lemma SeparatingLeft.ker_eq_bot : ker p = ⊥ :=
  separatingLeft_iff_ker_eq_bot.mp inst.elim

-- variable [Fact p.SeparatingRight] in
-- lemma SeparatingRight.ker_eq_bot : ker p.flip = ⊥ := by simp


-- ## IsSeparating

-- lemma IsSeparating.iff_ker_eq_bot : p.IsSeparating ↔ ker p = ⊥ := ker_eq_bot'.symm
-- lemma IsSeparating.ker_eq_bot (hp : p.IsSeparating) : ker p = ⊥ := iff_ker_eq_bot.mp hp

-- lemma IsFaithfulPair.isSeparating (hp : p.IsFaithfulPair) : p.flip.IsSeparating := by
--   intro x hpx
--   obtain ⟨_, hg⟩ := hp
--   exact hg x (by simp [← flip_apply, hpx])

-- @[deprecated SeparatingLeft (since := "")]
-- instance [inst : Fact p.IsFaithfulPair] : Fact p.flip.flip.IsFaithfulPair := inst
-- -- instance [inst : Fact p.flip.flip.IsFaithfulPair] : Fact p.IsFaithfulPair := inst

-- variable {R : Type*} [CommRing R]
-- variable {M : Type*} [AddCommGroup M] [Module R M]
-- variable {N : Type*} [AddCommGroup N] [Module R N]
-- variable {p : M →ₗ[R] N →ₗ[R] R}

-- def foo (hp : p.IsPerfPair) : N ≃ₗ[R] Dual R M := sorry

-- lemma IsSeparating.of_injective (hp : Injective p) : p.IsSeparating := by
--   simpa [IsSeparating.iff_ker_eq_bot] using ker_eq_bot_of_injective hp
-- instance [inst : Fact (Injective p)] : Fact p.IsSeparating :=
    -- ⟨IsSeparating.of_injective inst.elim⟩

-- instance [inst : Fact p.IsSeparating] : Fact p.flip.flip.IsSeparating := inst

-- lemma isSeparating_flip_of_isFaithfulPair (hp : p.IsFaithfulPair) : p.flip.IsSeparating := by
--   obtain ⟨g, hg⟩ := hp
--   intro x hx
--   simpa [← flip_apply p, hx] using hg x

-- instance [inst : Fact p.IsFaithfulPair] : Fact p.flip.IsSeparating :=
--     ⟨isSeparating_flip_of_isFaithfulPair inst.elim⟩
-- instance [inst : Fact p.flip.IsFaithfulPair] : Fact p.IsSeparating :=
--     ⟨isSeparating_flip_of_isFaithfulPair inst.elim⟩

-- variable [Module.Projective R M] in
-- instance : Fact (Dual.eval R M).IsSeparating := ⟨by simp [IsSeparating, eval_apply_eq_zero_iff]⟩

-- instance : Fact (Dual.eval R M).flip.IsSeparating := ⟨by simp [Dual.eval, IsSeparating]⟩

instance [inst : Fact (Surjective p)] : Fact (Surjective p.flip.flip) := inst

instance [inst : Fact (Injective p)] : Fact (Injective p.flip.flip) := inst

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] -- NOTE: AddCommMonoid suffices for some below
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

-- ## PRIORITY!
instance [inst : p.IsPerfPair] : Fact p.Nondegenerate := ⟨sorry⟩



lemma injective_flip_of_isFaithfulPair (hp : p.IsFaithfulPair) : Injective p.flip := by
  obtain ⟨g, hg⟩ := hp
  intro x y hxy
  simpa [← flip_apply p, hxy, sub_eq_zero] using hg (x - y)

instance [inst : Fact p.IsFaithfulPair] : Fact (Injective p.flip) :=
    ⟨injective_flip_of_isFaithfulPair inst.elim⟩

-- instance [inst : Fact p.flip.IsFaithfulPair] : Fact (Injective p) :=
--     ⟨injective_flip_of_isFaithfulPair inst.elim⟩

instance [inst : p.IsPerfPair] : Fact (Injective p) := ⟨inst.bijective_left.injective⟩
instance [inst : p.IsPerfPair] : Fact (Injective p.flip) := ⟨inst.bijective_right.injective⟩
instance [inst : p.flip.IsPerfPair] : Fact (Injective p) := ⟨inst.bijective_right.injective⟩
-- instance [inst : p.flip.IsPerfPair] : Fact (Injective p.flip) := inferInstance

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

lemma isFaithfulPair_of_toDual {ι : Type*} [DecidableEq ι] (b : Basis ι R M) :
    b.toDual.IsFaithfulPair := ⟨.id, fun _ => Dual.toDual_eq_zero⟩


-- ## SEPARATING

variable [Fact p.SeparatingLeft] in
@[simp] lemma SeparatingLeft.injective : Injective p := LinearMap.ker_eq_bot.mp ker_eq_bot

variable [Fact p.SeparatingRight] in
lemma SeparatingRight.injective : Injective p.flip := by simp

end CommRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

lemma isFaithfulPair_of_range_top (hp : range p = ⊤)
    : p.IsFaithfulPair := by classical
  obtain ⟨_, b⟩ := Free.exists_basis R N
  obtain ⟨p', hp'⟩ := LinearMap.exists_rightInverse_of_surjective p hp -- needs [Field R]
  use p' ∘ₗ b.toDual
  simp [← LinearMap.comp_assoc, hp']

lemma isFaithfulPair_of_surjective (hp : Surjective p) : p.IsFaithfulPair
  := isFaithfulPair_of_range_top <| range_eq_top_of_surjective p hp

instance [inst : Fact (Surjective p)] : Fact p.IsFaithfulPair
    := ⟨isFaithfulPair_of_surjective inst.elim⟩

lemma isFaithfulPair_of_id : IsFaithfulPair (R := R) (N := M) .id
  := isFaithfulPair_of_range_top range_id

instance instFactSurjectiveCoeIdId : Fact (Surjective (LinearMap.id (R := R) (M := M)))
  := ⟨surjective_id⟩
instance : Fact (Surjective (Dual.eval R M).flip)
  := instFactSurjectiveCoeIdId

instance instFactIsFaithfulPairIdId : Fact (IsFaithfulPair (R := R) (N := M) .id)
  := inferInstance -- ⟨isFaithfulPair_of_id⟩
instance : Fact (Dual.eval R M).flip.IsFaithfulPair := instFactIsFaithfulPairIdId

lemma isFaithfulPair_of_isPerfPair [p.IsPerfPair] : p.IsFaithfulPair :=
    isFaithfulPair_of_surjective (IsPerfPair.bijective_left p).surjective

instance [p.IsPerfPair] : Fact p.IsFaithfulPair := ⟨isFaithfulPair_of_isPerfPair⟩

instance [inst : p.IsPerfPair] : Fact (Surjective p) := ⟨inst.bijective_left.surjective⟩
instance [inst : p.IsPerfPair] : Fact (Surjective p.flip) := ⟨inst.bijective_right.surjective⟩


section IsReflexive

variable [IsReflexive R M]

lemma isFaithfulPair_of_eval : IsFaithfulPair (Dual.eval R M)
  := isFaithfulPair_of_surjective (bijective_dual_eval R M).surjective

instance : Fact (Dual.eval R M).IsFaithfulPair := ⟨isFaithfulPair_of_eval⟩
-- instance : Fact (IsFaithfulPair (R := R) (M := M) (flip .id)) :=
--     ⟨isFaithfulPair_of_eval⟩

end IsReflexive

section Module.Finite

-- instance [Module.Finite R M] [Fact p.IsFaithfulPair] : Module.Finite R N := by
--   sorry

-- instance [Module.Finite R M] [Fact p.IsFaithfulPair] : p.flip.IsFaithfulPair := by
--   sorry

end Module.Finite

end Field

end LinearMap
