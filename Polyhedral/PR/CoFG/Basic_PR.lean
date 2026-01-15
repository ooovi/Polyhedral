
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Submodule

section Ring

variable {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]

variable {α : Type*} {a b c : α} [Lattice α] [IsModularLattice α]

theorem _root_.Codisjoint.codisjoint_inf_right_of_codisjoint_inf_left [OrderTop α]
    (h : Codisjoint a b) (hsup : Codisjoint (a ⊓ b) c) : Codisjoint a (b ⊓ c) := by
  rw [← disjoint_toDual_iff] at *
  exact Disjoint.disjoint_sup_right_of_disjoint_sup_left h hsup

variable [BoundedOrder α] [ComplementedLattice α]

/-- A disjoint element can be enlarged to a complementary element. -/
lemma exists_isCompl_of_disjoint {a b : α} (hab : Disjoint a b) :
    ∃ a' : α, a ≤ a' ∧ IsCompl a' b := by
  obtain ⟨u, hu⟩ := ComplementedLattice.exists_isCompl (a ⊔ b)
  rw [sup_comm] at hu
  refine ⟨a ⊔ u, le_sup_left, ?_, ?_⟩
  · rw [disjoint_comm] at *
    exact hab.disjoint_sup_right_of_disjoint_sup_left hu.disjoint
  · rw [codisjoint_comm, ← codisjoint_assoc]
    exact hu.codisjoint

/-- A codisjoint element can be shrunk to a complementary element. -/
lemma exists_isCompl_of_codisjoint {a b : α} (hab : Codisjoint a b) :
    ∃ a' : α, a' ≤ a ∧ IsCompl a' b := by
  rw [← disjoint_toDual_iff] at *
  simpa using exists_isCompl_of_disjoint hab

end Ring

section DivisionRing

variable {M R : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]

/-- A disjoint submodule can be enlarged to a complementary submodule. -/
lemma exists_isCompl_of_disjoint' {S T : Submodule R M} (hST : Disjoint S T) :
    ∃ S' : Submodule R M, S ≤ S' ∧ IsCompl S' T :=
  exists_isCompl_of_disjoint hST

/-- A codisjoint submodule can be shrunk to a complementary submodule. -/
lemma exists_isCompl_of_codisjoint' {S T : Submodule R M} (hST : Codisjoint S T) :
    ∃ S' : Submodule R M, S' ≤ S ∧ IsCompl S' T :=
  exists_isCompl_of_codisjoint hST

end DivisionRing

end Submodule
