import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.FG



namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable {C F F₁ F₂ : PointedCone R M}


section opt

/- The minimum of `f/g` on a salient cone. -/
def opt (C : PointedCone R M) (f g : M →ₗ[R] R) (_ : ∀ x ∈ C, 0 ≤ g x ∧ (g x = 0 → x = 0)) :
    PointedCone R M where
  carrier := {x ∈ C | ∀ y ∈ C, f x * g y ≤ f y * g x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    refine ⟨C.add_mem ha.1 hb.1, ?_⟩
    intro y hy
    rw [add_mul, mul_add]
    exact add_le_add (ha.2 y hy) (hb.2 y hy)
  zero_mem' := by simp only [Set.mem_setOf_eq, zero_mem, map_zero, zero_mul, mul_zero, le_refl,
     implies_true, and_self]
  smul_mem' := by
    intro a x hx
    refine ⟨C.smul_mem a.2 hx.1, ?_⟩
    intro y hy
    by_cases! h : a ≤ 0
    · simp [nonpos_iff_eq_zero.mp h]
    simp only [LinearMap.map_smul_of_tower, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    exact (smul_le_smul_iff_of_pos_left h).mpr <| hx.2 y hy

lemma IsSalient.of_opt (C : PointedCone R M) (_ g : M →ₗ[R] R)
    (hg : ∀ x ∈ C, 0 ≤ g x ∧ (g x = 0 → x = 0)) : C.Salient := by
  intro x hx x_ne_0 hxn
  have h1 := lt_of_le_of_ne (hg _ hx).1 (fun h ↦ x_ne_0 <| (hg _ hx).2 (Eq.symm h))
  have h2 := lt_of_le_of_ne
    (hg _ hxn).1 (fun h ↦ x_ne_0 (neg_eq_zero.mp <| (hg _ hxn).2 <| Eq.symm h))
  simp only [_root_.map_neg, Left.neg_pos_iff] at h2
  linarith

lemma IsFaceOf.of_opt (C : PointedCone R M) (f g : M →ₗ[R] R)
    (hg : ∀ x ∈ C, 0 ≤ g x ∧ (g x = 0 → x = 0)) : (C.opt f g hg).IsFaceOf C := by
  refine { le := fun _ hx ↦ hx.1, mem_of_smul_add_mem := ?_ }
  intro x y a hx hy ha ⟨h2, h⟩
  by_cases! x_ne_0 : x = 0
  · rw [x_ne_0]; exact zero_mem (C.opt f g hg)
  by_cases! t_ne_0 : a • x + y = 0
  · exfalso
    apply (IsSalient.of_opt C f g hg) (a • x)
    · exact C.smul_mem (le_of_lt ha) hx
    · exact smul_ne_zero (ne_of_gt ha) x_ne_0
    rw [neg_eq_of_add_eq_zero_right t_ne_0]
    exact hy
  refine ⟨hx, fun z hz ↦ ?_⟩
  have : g x > 0 := lt_of_le_of_ne (hg _ hx).1 (fun h ↦ x_ne_0 <| (hg _ hx).2 (Eq.symm h))
  have t1 := h x hx
  have t2 := h y hy
  have t4 := (mul_le_mul_iff_of_pos_left this).mpr <| (h z hz)
  simp only [map_add, map_smul, smul_eq_mul] at t1 t2 t4
  have local_lemma : ∀ {a b c d e : R}, e > 0 → a ≤ b → c ≤ d → e * a + c = e * b + d → a = b :=
    fun _ _ _ _ ↦ by nlinarith
  have t3 : (a * f x + f y) * g x = f x * (a * g x + g y) := local_lemma ha t1 t2 (by ring)
  have : a * g x + g y > 0 := by
    simpa only [gt_iff_lt, map_add, map_smul, smul_eq_mul] using
      lt_of_le_of_ne (hg _ h2).1 (fun h ↦ t_ne_0 <| (hg _ h2).2 (Eq.symm h))
  apply (mul_le_mul_iff_of_pos_left this).mp
  nth_rw 3 [mul_comm] at t3
  rw [← mul_assoc, ← t3]
  linarith

lemma FG.opt_neq_bot (C : PointedCone R M) (hC : C.FG) (f g : M →ₗ[R] R)
    (hg : ∀ x ∈ C, 0 ≤ g x ∧ (g x = 0 → x = 0)) : C.opt f g hg ≠ ⊥ := sorry

end opt

/- For every ray `x` of the span of a set `s`, there is a member of `s` that also spans the ray. -/
lemma IsFaceOf.span_ray {s : Set M} {x : M} (hx : x ≠ 0)
    (hspan : (span R {x}).IsFaceOf (span R s)) : ∃ y ∈ s, ∃ c : R, 0 < c ∧ y = c • x := by
  have h := hspan.span_inter_face_span_inf_face
  have ⟨y, hy, hy0⟩ : ∃ w ∈ s ∩ (span R {x}), w ≠ 0 := by
    by_contra H
    absurd hx
    push_neg at H
    simp only [← Set.mem_singleton_iff] at H
    simpa [h] using Submodule.span_mono (R := {c : R // 0 ≤ c}) H
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Submodule.mem_span_singleton, Subtype.exists,
    Nonneg.mk_smul, exists_prop] at hy
  obtain ⟨hys, a, ha, rfl⟩ := hy
  exact ⟨_, hys, a, lt_of_le_of_ne ha (fun h => hy0 (by simp [← h])), rfl⟩


open Module in
-- TODO: this proof uses FG only at one point: to show that opt is non-empty. This should
--  generalize to dual-closed.
/- Krein-Milman theorem: Every finitely generated cone is spanned by a finite set of its rays. -/
lemma FG.krein_milman (hfg : C.FG) (hsal : C.Salient) :
    ∃ s : Finset M, span R s = C ∧ ∀ x ∈ s, (span R {x}).IsFaceOf C := by
  classical
  let ⟨s, hs⟩ := hfg
  by_cases hs' : s = ∅
  · exact ⟨∅, by simp [← hs, hs']⟩
  by_contra! h
  let t := s.filter fun x => (span R {x}).IsFaceOf C
  specialize h t
  have hts : t ⊆ s := by simp [t]
  have hst : ¬(s : Set M) ⊆ span R (t : Set M) := by
    by_contra h'
    have h' := Submodule.span_mono (R := {c : R // 0 ≤ c}) h'
    have h'' := Submodule.span_mono (R := {c : R // 0 ≤ c}) hts
    simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self] at h'
    rw [← le_antisymm h' h'', hs] at h
    simp [t, and_assoc] at h
  obtain ⟨x, hxs, hxt⟩ := Set.not_subset.mp hst
  have hx : x ∈ C := by
    rw [← hs]
    exact subset_span hxs
  obtain ⟨f, hf, hf'⟩ := FG.farkas (Dual.eval R M) hxt
  rw [← hs] at hsal
  -- TODO exists_dual_pos₀ is a hole
  -- Der beweis würde benutzen dass die cone ein nicht-leeres relint hat. ABER: quick and dirty geht
  -- es schneller für FG cones. Man geht zur dualen cone, die ist auch FG (zumindest in endlich dim,
  -- was euch interessiert), und g ist dann die summe aller erzeuger der dual cone. Wenn du nicht in
  -- endl dim bist musst du die duale cone erst zerlegen in FG + lineal (dafür gibts ein lemma
  -- irgendwo) und dann die summe der erzeuger des FG anteils nehmen
  obtain ⟨g, hg⟩ := exists_dual_pos₀ (Dual.eval R M) hsal
  rw [hs] at hsal
  simp only [Dual.eval_apply, gt_iff_lt] at hf hf' hg
  rw [hs] at hg
  let F := C.opt f g hg
  have hF : F.IsFaceOf C := IsFaceOf.of_opt C f g hg
  have hF' := opt_neq_bot C hfg f g hg
  have hFsal := Salient.of_le_salient hsal hF.le
  obtain ⟨r, hr0, hrF⟩ := exists_ray (hF.fg_of_fg hfg) hF' hFsal
  have hr := IsFaceOf.trans hrF hF
  rw [← hs] at hr
  obtain ⟨w, hws, c, hc', h⟩ := hr.span_ray hr0
  simp only [SetLike.mem_coe] at hws
  have hc0 := (ne_of_lt hc').symm
  have hrw : r = c⁻¹ • w := by
    subst h hs
    simp [smul_smul, hc0]
  rw [hrw] at hr
  rw [span_singleton_smul_eq (inv_pos.mpr hc')] at hr
  have hwt : w ∈ t := by
    simpa [Finset.mem_filter, t] using ⟨hws, hs ▸ hr⟩
  have hwF : r ∈ F := by
    have : r ∈ span R {r} := by simp
    exact hrF.le this
  have hwF : w ∈ F := by
    rw [h]
    exact F.smul_mem (le_of_lt hc') hwF
  simp only [opt, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    F] at hwF
  have hgw : 0 < g w := by
    have hw0 : w ≠ 0 := by
      rw [h]
      exact smul_ne_zero hc0 hr0
    by_contra! h
    have hgw := hg w hwF.1
    have hgw' := le_antisymm hgw.1 h
    have := hgw.2 hgw'.symm
    absurd hxt
    contradiction
  have hwF := hwF.2 x hx
  have : 0 ≤ f w * g x := mul_nonneg (hf' w hwt) (hg x hx).1
  have : f x * g w < 0 := mul_neg_of_neg_of_pos hf hgw
  linarith

end PointedCone
