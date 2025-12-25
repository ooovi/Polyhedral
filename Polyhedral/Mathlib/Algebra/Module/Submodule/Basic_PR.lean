
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.OmegaCompletePartialOrder

namespace Submodule

section Semiring

variable {R : Type*} [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {S : Type*} [Semiring S] [Module S R] [Module S M] [IsScalarTower S R M]

lemma subtype_restrictScalars (p : Submodule R M) :
    p.subtype.restrictScalars S = (p.restrictScalars S).subtype := rfl

variable (S)

lemma restrictScalars_mono {s t : Submodule R M} (hST : s ≤ t) :
    s.restrictScalars S ≤ t.restrictScalars S := (restrictScalarsEmbedding S R M).monotone hST

@[simp] lemma restrictScalars_inf {s t : Submodule R M} :
    (s ⊓ t).restrictScalars S = (s.restrictScalars S) ⊓ (t.restrictScalars S) := by
  ext x; simp

@[simp] lemma restrictScalars_sup {s t : Submodule R M} :
    (s ⊔ t).restrictScalars S = (s.restrictScalars S) ⊔ (t.restrictScalars S):= by
  ext x; simp [mem_sup]

@[simp] lemma restrictScalars_sSup {s : Set (Submodule R M)} :
    (sSup s).restrictScalars S = sSup (restrictScalars S '' s) :=
  (restrictScalarsLatticeHom S R M).map_sSup' s

@[simp] lemma restrictScalars_sInf {s : Set (Submodule R M)} :
    (sInf s).restrictScalars S = sInf (restrictScalars S '' s) :=
  (restrictScalarsLatticeHom S R M).map_sInf' s

end Semiring

section Ring

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable (R) in
@[simp] lemma submodule_span_pm_pair (x : M) :
    Submodule.span R {-x, x} = Submodule.span R {x} := by
  rw [← Set.union_singleton, Submodule.span_union]; simp

end Ring

end Submodule
