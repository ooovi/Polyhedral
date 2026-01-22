import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.OmegaCompletePartialOrder

namespace Submodule

section Semiring

open Function LinearMap Module

variable {M S R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

-- Is this the better name?
protected alias span_gi := Submodule.gi

-- Q: should `Submodule.span_union` be a simp theorem? Yael says possibly
example (S S' : Set M) : span R (S ∪ S') = (span R S) ⊔ (span R S')
  := Submodule.span_union S S'

@[simp] theorem span_union' (S S' : Submodule R M) : span R (S ∪ S') = S ⊔ S'
  := (Submodule.gi R M).l_sup_u S S'

-- span_sup'
example (S S' : Submodule R M) : span R (S ⊔ S' : Submodule R M) = S ⊔ S' := span_eq _

@[simp] theorem span_inter_le (s t : Set M) : span R (s ∩ t) ≤ span R s ⊓ span R t :=
    le_inf (span_mono Set.inter_subset_left) (span_mono Set.inter_subset_right)

@[simp] theorem span_inter (S S' : Submodule R M) : span R (S ∩ S') = S ⊓ S'
    := (Submodule.gi R M).l_inf_u S S'

alias span_inf := span_inter

theorem span_sSup (s : Set (Submodule R M)) :
    span R (sSup (SetLike.coe '' s)) = sSup s := (Submodule.gi R M).l_sSup_u_image s

theorem span_sInf (s : Set (Submodule R M)) :
    span R (sInf (SetLike.coe '' s)) = sInf s := (Submodule.gi R M).l_sInf_u_image s

-- span_iSup

-- span_iInf

theorem span_biUnion (s : Set (Submodule R M)) :
    span R (⋃ S ∈ s, S) = sSup s := by simpa using span_sSup s

theorem span_biInter (s : Set (Submodule R M)) :
    span R (⋂ S ∈ s, S) = sInf s := by simpa using span_sInf s

alias span_iInter := span_biInter

end Semiring

end Submodule
