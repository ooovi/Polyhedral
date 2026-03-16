import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank

namespace PointedCone

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

lemma ray_of_rank_one (hS : C.Salient) (h : C.rank = 1) : ∃ x : M, C = span R {x} := by
  have : C ≠ ⊥ := fun h' ↦ by simp [bot_iff_rank_zero.mpr h'] at h
  obtain ⟨x, hxC, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
  refine ⟨x, le_antisymm ?_ (by simp [hxC]) ⟩
  intro y hy
  by_cases hyx : ∃ a : R, y = a • x
  · obtain ⟨a, rfl⟩ := hyx
    by_cases ha0 : 0 ≤ a
    · exact smul_mem ({ c // 0 ≤ c } ∙ x) ha0 <| Submodule.mem_span_singleton_self x
    exfalso
    have ha : a < 0 := lt_of_not_ge ha0
    apply hS x hxC hx0
    have hnegx : -x = (-a⁻¹) • (a • x) := by
      have ha' : a ≠ 0 := ne_of_lt ha
      simp [smul_smul, ha']
    rw [hnegx]
    exact smul_mem C (le_of_lt <| neg_pos.2 <| inv_lt_zero.mpr ha) hy
  let f : Fin 2 → C.linSpan :=
    ![(⟨x, Submodule.mem_span_of_mem hxC⟩ : C.linSpan), ⟨y, Submodule.mem_span_of_mem hy⟩]
  have hf0 : f 0 ≠ 0 := by
    intro hf0
    apply hx0
    simpa [f] using congrArg Subtype.val hf0
  have hlin : LinearIndependent R f := by
    refine (LinearIndependent.pair_iff' hf0).2 ?_
    intro a hax
    apply hyx
    refine ⟨a, ?_⟩
    exact (Subtype.ext_iff.mp hax).symm
  have : C.rank ≥ 2 := Module.le_rank_iff.2 ⟨f, hlin⟩
  simp [h] at this

end DivisionRing

section Ring

variable {R : Type*} [Ring R] [StrongRankCondition R] [PartialOrder R] [IsOrderedRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]

lemma rank_one_of_ray {x : M} (hx : x ≠ 0) :
    (span R {x}).rank = 1 := by
  have hlin : LinearIndependent R (fun _ : Unit => x) :=
    LinearIndependent.of_subsingleton () hx
  have hr := rank_span (R := R) (M := M) hlin
  have hspan : Submodule.span R (Set.range (fun _ : Unit => x)) = (span R {x}).linSpan := by
    simp [PointedCone.linSpan, Set.range_const]
  rw [hspan] at hr
  rw [PointedCone.rank]
  simpa using hr

lemma finrank_one_of_ray {x : M} (hx : x ≠ 0) :
    (span R {x}).finrank = 1 := by
  simpa [Module.finrank, Cardinal.toNat_eq_one] using rank_one_of_ray hx

end Ring

end PointedCone
