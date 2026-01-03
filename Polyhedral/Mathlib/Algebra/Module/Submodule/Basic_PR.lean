
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Submodule

section Ring

variable {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]

lemma disjoint_sup_assoc_of_disjoint {S T U : Submodule R M}
    (hST : Disjoint S T) (hSTU : Disjoint (S ⊔ T) U) : Disjoint S (T ⊔ U) := by
  intro V hVS hVTU x hxV
  have hxS := hVS hxV
  obtain ⟨y, hyT, z, hzU, rfl⟩ := mem_sup.mp (hVTU hxV)
  have h := add_mem
    ((SetLike.le_def.mp le_sup_left) (neg_mem hyT))
    ((SetLike.le_def.mp le_sup_right) hxS)
  simp only [sup_comm, neg_add_cancel_left] at h
  simp only [disjoint_def.mp hSTU _ h hzU, add_zero, mem_bot] at ⊢ hxS
  exact disjoint_def.mp hST _ hxS hyT

lemma codisjoint_inf_assoc_of_codisjoint {S T U : Submodule R M}
    (hST : Codisjoint S T) (hSTU : Codisjoint (S ⊓ T) U) : Codisjoint S (T ⊓ U) := by
  intro V hSV hTUV x
  simp only [mem_top, forall_const]
  obtain ⟨s, t, hsS, htT, rfl⟩ := codisjoint_iff_exists_add_eq.mp hST x
  obtain ⟨st, u, hstST, huU, H⟩ := codisjoint_iff_exists_add_eq.mp hSTU t
  rw [← H, ← add_assoc]
  rw [mem_inf] at hstST
  have hu : u ∈ T := by
    rw [add_comm] at H
    rw [eq_add_neg_of_add_eq H]
    exact add_mem htT (neg_mem hstST.2)
  refine add_mem (hSV <| add_mem hsS hstST.1) (hTUV ?_)
  exact mem_inf.mpr ⟨hu, huU⟩

end Ring

section DivisionRing

variable {M R : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]

/-- A disjoint submodule can be enlarged to a complementary submodule. -/
lemma exists_isCompl_of_disjoint {S T : Submodule R M} (hST : Disjoint S T) :
    ∃ S' : Submodule R M, S ≤ S' ∧ IsCompl S' T := by
  obtain ⟨U, hU⟩ := exists_isCompl (S ⊔ T)
  use S ⊔ U
  constructor
  · exact le_sup_left
  constructor
  · rw [sup_comm] at hU
    rw [disjoint_comm] at hST
    have h := disjoint_sup_assoc_of_disjoint hST hU.disjoint
    exact disjoint_comm.mp h
  · rw [codisjoint_comm, ← codisjoint_assoc, sup_comm]
    exact hU.codisjoint

/-- A codisjoint submodule can be shrunk to a complementary submodule. -/
lemma exists_isCompl_of_codisjoint {S T : Submodule R M} (hST : Codisjoint S T) :
    ∃ S' : Submodule R M, S' ≤ S ∧ IsCompl S' T := by
  obtain ⟨U, hU⟩ := exists_isCompl (S ⊓ T)
  use S ⊓ U
  constructor
  · exact inf_le_left
  constructor
  · rw [disjoint_comm, ← disjoint_assoc, inf_comm]
    exact hU.disjoint
  · rw [inf_comm] at hU
    rw [codisjoint_comm] at hST
    have h := codisjoint_inf_assoc_of_codisjoint hST hU.codisjoint
    exact codisjoint_comm.mp h

end DivisionRing

end Submodule
