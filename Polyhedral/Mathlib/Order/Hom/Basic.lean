import Mathlib.Order.Hom.Basic

namespace OrderIso

variable {α β : Type*}
variable [Preorder α] [Preorder β]

@[simp, to_dual self]
theorem covBy_iff_covBy (e : α ≃o β) {x y : α} : x ⋖ y ↔ e x ⋖ e y := by
  refine ⟨fun h ↦ ⟨e.lt_iff_lt.mpr h.1, ?_⟩, fun h ↦ ⟨e.lt_iff_lt.mp h.1, ?_⟩⟩
  · refine fun c' hc' hcon ↦ ?_
    refine h.2 ?_ <| e.symm_apply_apply _ ▸ e.symm.strictMono hcon
    convert e.symm_apply_apply _ ▸ e.symm.strictMono hc'
  · exact fun c' hc' hcon ↦ h.2 (e.strictMono hc') (e.strictMono hcon)

end OrderIso
