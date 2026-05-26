import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Basic
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Set.Hull

section Convexity

namespace PointedCone

open Convexity

section Ring

variable {R M : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
    [Module R M] {s : Set M}

lemma isConvexSet (P : PointedCone R M) :
    Convexity.IsConvexSet R (P : Set M) := by
  intro w hw
  rw [Convexity.sConvexComb_eq_sum w]
  refine P.finsuppSum_mem _ _ (fun i r ↦ r • i) (fun c hc ↦ ?_)
  exact P.smul_mem (w.weights_nonneg c) <| hw (Finsupp.mem_support_iff.mpr hc)

open PointedCone in
theorem hull_convexHull_eq_hull (t : Set M) :
    hull R t = hull R (Convexity.convexHull R t) := by
  ext x; constructor <;> intro h
  · exact Submodule.span_mono (by simpa [Convexity.convexHull] using fun _ a _ ↦ a) h
  apply Submodule.mem_span.mp h
  simp only [Convexity.convexHull, ClosureOperator.ofCompletePred_apply, Set.le_eq_subset,
    Set.iInf_eq_iInter]
  intro a am
  simp only [Set.mem_iInter, Subtype.forall, and_imp, SetLike.mem_coe, Submodule.mem_span] at ⊢ am
  exact fun p hp ↦ am _ hp <| isConvexSet p

end Ring

section Field

variable {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
    [Module R M] {s : Set M}

open Pointwise Set

protected theorem _root_.IsConvexSet.add_smul (h_conv : Convexity.IsConvexSet R s) {p q : R}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p + q) • s = p • s + q • s := sorry

/-- The cone hull of a convex set is the union of the closed halflines through that set. -/
lemma mem_hull_iff_of_convex (hs : s.Nonempty) (hc : Convexity.IsConvexSet R s) (x : M) :
    x ∈ hull R s ↔ x ∈ Ici (0 : R) • s where
  mp hx := hull_min (C := {
              carrier := {y | ∃ r : R, 0 ≤ r ∧ y ∈ r • s}
              smul_mem' := by
                intro c x ⟨r, rpos, hr⟩
                use c.val • r, mul_nonneg c.prop rpos
                obtain ⟨m, hm, rfl⟩ := hr
                exact ⟨m, hm, by simp [mul_smul]⟩
              add_mem' := by
                rintro y₁ y₂ ⟨r₁, hr₁, hy₁⟩ ⟨r₂, hr₂, hy₂⟩
                refine ⟨r₁ + r₂, add_nonneg hr₁ hr₂, ?_⟩
                rw [IsConvexSet.add_smul hc hr₁ hr₂]
                exact add_mem_add hy₁ hy₂
              zero_mem' := by
                use 0; simpa using ⟨hs.choose, hs.choose_spec, zero_smul R (Exists.choose hs)⟩
            }) (fun y hy ↦ ⟨1, by simpa⟩) hx
  mpr h := by
    obtain ⟨r, hr, y, hy, rfl⟩ := h
    exact (hull R s).smul_mem (Set.mem_Ici.mp hr) <| subset_hull hy

/-- Every nonzero member of the conic hull of a convex set is a pos. smultiple of a set member. -/
theorem mem_hull_iff_mem_pos_smul_of_convex_nonzero {x : M} {s} (hc : IsConvexSet R s)
    (hx : x ≠ 0) :
    x ∈ hull R s ↔ x ∈ Ioi (0 : R) • s := by
  by_cases hs : s.Nonempty
  · constructor <;> intro h
    · obtain ⟨r, rpos, hr⟩ := (mem_hull_iff_of_convex hs hc _).mp h
      rcases eq_or_ne 0 r with rfl | h
      · simp_all
      exact ⟨r, lt_of_le_of_ne rpos h, hr⟩
    · simp [mem_hull_iff_of_convex hs hc, Set.smul_subset_smul_right Ioi_subset_Ici_self h]
  · simp [Set.not_nonempty_iff_eq_empty.mp hs, hx]

theorem hull_eq_smul (hs : s.Nonempty) (hc : IsConvexSet R s) :
    hull R s = Ici (0 : R) • s := by
  ext x; exact mem_hull_iff_of_convex hs hc x

/-- If there is a linear map that is positive on the entire cone except 0, the cone is the sMul-span
of any positive level set of the map. -/
lemma eq_pos_smul_base {C : PointedCone R M} {f : M →ₗ[R] R} {r : R} (hf : ∀ x ∈ C, x ≠ 0 → 0 < f x)
    (hr : 0 < r) :
    (C : Set M) \ {0} = Set.Ioi (0 : R) • ((C : Set M) ∩ f ⁻¹' {r}) := by
  ext x
  constructor
  · intro ⟨hxC, hx0⟩
    refine ⟨r⁻¹ • f x, smul_pos (inv_pos.mpr hr) <| hf x hxC hx0, (r • (f x)⁻¹) • x, ⟨?_, ?_⟩, ?_⟩
    · exact C.smul_mem (smul_pos hr <| inv_pos.mpr (hf _ hxC hx0)).le hxC
    · simp [inv_mul_cancel₀ (ne_of_gt (hf x hxC hx0)), mul_assoc]
    · simp only [smul_eq_mul, smul_smul]
      field_simp [ne_of_gt (hf x hxC hx0)]
      exact MulAction.one_smul x
  · rintro ⟨r, hri, y, ⟨hyC, hfy⟩, rfl⟩
    have hy0 : y ≠ 0 := by intro hc; simp only [hc, mem_preimage, map_zero,
      Set.mem_singleton_iff] at hfy; exact hr.ne hfy
    exact ⟨C.smul_mem (mem_Ioi.mp hri).le hyC, by simp [ne_of_gt hri, hy0]⟩

/-- If there is a linear map that is positive on the entire cone except 0, the cone is the closed
sMul-span of any positive level set of the map. -/
lemma eq_nonneg_smul_base {C : PointedCone R M} {f : M →ₗ[R] R} {r : R}
    (hf : ∀ x ∈ C, x ≠ 0 → 0 < f x) (hr : 0 < r)
    (hC : C ≠ ⊥) :
    C = Set.Ici (0 : R) • ((C : Set M) ∩ f ⁻¹' {r}) := by
  ext x
  by_cases hx : x = 0
  · subst hx
    simp only [SetLike.mem_coe, zero_mem, true_iff]
    use 0, le_rfl
    simp only [mem_inter_iff, SetLike.mem_coe, mem_preimage, mem_singleton_iff, zero_smul, and_true]
    obtain ⟨x, hx⟩ := C.ne_bot_iff.mp hC
    use r • (f x)⁻¹ • x
    have fxpos : 0 < f x := hf x hx.1 hx.2
    simp only [← smul_assoc, smul_eq_mul, map_smul]
    refine ⟨C.smul_mem (mul_pos hr (inv_pos.mpr fxpos)).le hx.1, ?_⟩
    simp [mul_assoc, inv_mul_cancel₀ fxpos.ne.symm]
  · constructor <;> intro h
    · apply Set.smul_subset_smul_right Ioi_subset_Ici_self
      exact eq_pos_smul_base hf hr ▸ mem_diff_singleton.mpr ⟨h, hx⟩
    · obtain ⟨_, hr, _, hy, b⟩ := h
      simpa [← b] using C.smul_mem hr (mem_of_mem_inter_left hy)

end Field

end PointedCone

end Convexity
