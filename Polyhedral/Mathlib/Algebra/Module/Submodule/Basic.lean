import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Defs

namespace Submodule

variable {E S R : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid E] [Module S R] [Module R E] [Module S E] [IsScalarTower S R E]

section RestrictedScalar

lemma restrictedScalars_fg_of_fg [Module.Finite S R] {s : Submodule R E} (hfg : s.FG) :
    (s.restrictScalars S).FG := by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans R s

lemma restrictedScalars_fg_iff_fg [Module.Finite S R] {s : Submodule R E} :
    (s.restrictScalars S).FG ↔ s.FG := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h
    use t
    sorry
  · intro _;
    rw [← Module.Finite.iff_fg] at *
    exact Module.Finite.trans R s

-- Converse ?
lemma span_scalars_FG [Module.Finite S R] {s : Submodule S E} (hfg : s.FG) :
    (span R (M := E) s).FG := by
  obtain ⟨t, ht⟩ := hfg
  use t; rw [← ht, Submodule.span_span_of_tower]

@[simp]
lemma restrictScalars_inf {s t : Submodule R E} :
    (s ⊓ t).restrictScalars S = (s.restrictScalars S) ⊓ (t.restrictScalars S) := by
  ext x; simp

@[simp]
lemma restrictScalars_sup {s t : Submodule R E} :
    (s ⊔ t).restrictScalars S = (s.restrictScalars S) ⊔ (t.restrictScalars S):= by
  ext x; simp [mem_sup]

end RestrictedScalar

example (S S' : Set E) : span R (S ∪ S') = (span R S) ⊔ (span R S')
  := Submodule.span_union S S' -- should `Submodule.span_union` be a simp lemma? Yael says possibly
example (S S' : Submodule R E) : span R (S ⊔ S' : Submodule R E) = S ⊔ S'
  := by simp

@[simp] lemma span_union' (S S' : Submodule R E) : span R (S ∪ S') = S ⊔ S'
  := by rw [Submodule.span_union]; simp
@[simp] lemma span_inter (S S' : Submodule R E) : span R (S ∩ S') = S ⊓ S'
    := by rw [←coe_inf, span_eq]

example (S S' : Submodule R E) : (S ∩ S' : Set E) = S ⊓ S'
  := by simp -- only [coe_inf]

/-- Restricts a submodule S to a submodule T. -/
def restrict (S T : Submodule R E) : Submodule R T := S.comap T.subtype
-- def restrict_set (S : Set E) (T : Submodule R E) : Set T := S.comap T.subtype

@[simps]
protected abbrev copy' (s : Set E) (hs : ∃ p : Submodule R E, s = p) :
    Submodule R E where
  carrier := s
  zero_mem' := by obtain ⟨p, rfl⟩ := hs; exact p.zero_mem'
  add_mem' := by obtain ⟨p, rfl⟩ := hs; exact p.add_mem'
  smul_mem' := by obtain ⟨p, rfl⟩ := hs; exact p.smul_mem'

theorem copy_eq' (s : Set E) (hs : ∃ p : Submodule R E, s = ↑p) : Submodule.copy' s hs = s := rfl

end Submodule
