import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Finiteness.Basic


import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed

/-
theorem 2.7 from ziegler page 57:
(i) For every polytope P the face poset L(P) is a graded lattice of length
dim(P) + 1, with rank function r(F) = dim(F) + 1.
(ii) Every interval [G, F] of L(P) is the face lattice of a convex polytope
of dimension r(F) − r(G) − 1.

proof:
part (ii).
- assume F = P, by Prop 2.3(iii) (faces of F are exactly the faces of P that are contained in F)
- if G = ∅, then everything is clear
- If G ̸= ∅, it has a vertex v ∈ G by Prop 2.2(i) (krein milman, Every polytope is the convex
 hull of its vertices: P = conv(vert(P)).)
- it is a vertex of P by Prop 2.3(iii)
- Prop 2.4: There is a bijection between the k-dimensional faces of P that contain v, and the
 (k−1)-dimensional faces of P/v, given by
 π : F ↦ F ∩ {x : cx = c₁}
 σ : F' ↦ P ∩ aff ({v} ∪ F')
- face lattice of P/v is isomorphic to interval [{v}, P] of the face lattice L(P), by Prop 2.4
- done by induction on dim(G).

part (i).
- G ⊂ F faces of P
- monotonicity:
  - then G = P ∩ aff(G) ⊆ P ∩ aff(F) = F by Prop 2.3(iv) (every face has a supportin hyperplane)
  - so aff(G) ⊂ aff(F), and thus dim(G) < dim(F)
- covering:
  - let dim(F)−dim(G) ≥ 2, show there is a face H ∈ L(P) with G ⊂ H ⊂ F
  - by part (ii) the interval [G, F] is the face lattice of a polytope of dimension at least 1
  - so it has a vertex, which yields the desired H.


stuff we need:
- faces of F are exactly the faces of P that are contained in F (`IsFaceOf.trans`)
- every non-⊥ cone has a vertex (`FG.exists_ray` below)
- bijection between the k-dimensional faces of P that contain v, and the
 (k−1)-dimensional faces of P/v
- every face has a supporting hyperplane (`IsFaceOf.FG.exposed` below)
-/


namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

/- Farkas lemma for finitely generated cones: for any point `x` not in the span of a finite set `s`,
  there exists a hyperplane `φ` separating `x` from `span R s`. -/
variable (p) [Fact p.SeparatingLeft] in
lemma FG.farkas {s : Finset M} {x : M} (h : x ∉ span R s) :
    ∃ φ : N, 0 > p x φ ∧ ∀ y ∈ s, 0 ≤ p y φ := by
  let ⟨φ, hφ, h⟩ := PointedCone.farkas (FG.isDualClosed p ⟨s, rfl⟩) h
  exact ⟨φ, hφ, fun y hy => h y (subset_span hy)⟩


variable {C F F₁ F₂ : PointedCone R M}

lemma exists_fg_span_subset_face {s : Finset M} (hF : F.IsFaceOf (span R s)) :
    ∃ t ⊆ s, span R t = F := by
  use (s.finite_toSet.inter_of_left F).toFinset
  simp [IsFaceOf.span_inter_face_span_inf_face hF]

/-- Faces of FG cones are FG. -/
lemma IsFaceOf.fg_of_fg (hC : C.FG) (hF : F.IsFaceOf C) : F.FG := by
  obtain ⟨_, rfl⟩ := hC
  let ⟨t, _, tt⟩ := exists_fg_span_subset_face hF
  use t, tt

section exposed

-- TODO: can we reduce assumptions?
variable (p) [Fact (Function.Surjective p.flip)] in
lemma IsFaceOf.FG.subdual_subdual (hC : C.FG) (hF : F.IsFaceOf C) :
    subdual p.flip (dual p C) (subdual p C F) = F := by
  repeat rw [subdual_def]
  rw [FG.dual_flip_dual p hC]
  rw [← dual_span_lineal_dual]
  rw [Submodule.coe_inf, Submodule.coe_restrictScalars]
  nth_rw 3 [← PointedCone.ofSubmodule_coe]
  rw [FGDual.dual_inf_dual_sup_dual ?_ ?_]
  · rw [Submodule.coe_restrictScalars, dual_eq_submodule_dual]
    rw [FG.dual_flip_dual p hC]
    nth_rw 2 [← Submodule.dual_span]
    rw [Submodule.dual_flip_dual p]
    have H : (C ⊔ F.linSpan).lineal = F.linSpan := by
      sorry
    rw [H]
    exact hF.inf_linSpan
  · simpa using FG.dual_fgdual _ hC
  · rw [LinearMap.flip_flip, coe_fgdual_iff, ← Submodule.dual_span]
    exact Submodule.FG.dual_fgdual _ (submodule_span_fg <| hF.fg_of_fg hC)

open Module in
/-- Every face of an FG cone is exposed. -/
lemma IsFaceOf.FG.exposed (hC : C.FG) (hF : F.IsFaceOf C) :
    F.IsExposedFaceOf C := by
  wlog _ : Module.Finite R M with exposed -- reduction to finite dimensional case
  · let S : Submodule R M := .span R C
    have H := exposed (FG.restrict_fg S hC) (IsFaceOf.restrict S hF)
      (Finite.iff_fg.mpr <| submodule_span_fg hC)
    have hC : C ≤ Submodule.span R (C : Set M) := Submodule.le_span
    simpa [S, hC, le_trans hF.le hC] using H.embed
  rw [← FG.dual_flip_dual (Dual.eval R M) hC]
  rw [← subdual_subdual (Dual.eval R M) hC hF]
  exact .subdual_dual _ <| .subdual_dual _ hF

end exposed


section opt

/- The minimum of `f/g` on a salient cone. -/
def opt (C : PointedCone R M) (f g : M →ₗ[R] R) (hg : ∀ x ∈ C, 0 ≤ g x ∧ (g x = 0 → x = 0)) :
    PointedCone R M where
  carrier := {x ∈ C | ∀ y ∈ C, f x * g y ≤ f y * g x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    constructor
    · exact C.add_mem ha.1 hb.1
    intro y hy
    have ha := ha.2 y hy
    have hb := hb.2 y hy
    sorry
  zero_mem' := sorry
  smul_mem' := sorry

lemma IsFaceOf.of_opt (C : PointedCone R M) (f g : M →ₗ[R] R)
    (hg : ∀ x ∈ C, 0 ≤ g x ∧ (g x = 0 → x = 0)) : (C.opt f g hg).IsFaceOf C := sorry

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


open Submodule in
/-- If a point `x` does not lie in a cone `C` but together with `C` spans a salient cone, then
  `x` spans a face of `span R (C ∪ {x})`. -/
lemma span_singleton_isFaceOf_sup_singleton_of_not_mem {C : PointedCone R M} {x : M}
    (hx : x ∉ C) (hC : (C ⊔ span R {x}).Salient) : (span R {x}).IsFaceOf (C ⊔ span R {x}) := by
  rw [IsFaceOf.iff_mem_of_add_mem]
  constructor
  · exact le_sup_right
  intro y z hy hz hyz
  simp only [mem_sup, mem_span_singleton, Subtype.exists, Nonneg.mk_smul, exists_prop,
    exists_exists_and_eq_and] at *
  obtain ⟨y', hy', a, _, hy⟩ := hy
  obtain ⟨z', hz', b, _, hz⟩ := hz
  obtain ⟨c, _, hyz⟩ := hyz
  rw [← hy, ← hz, add_assoc, ← sub_eq_iff_eq_add] at hyz
  nth_rw 2 [add_comm] at hyz
  rw [← add_assoc, ← add_smul, sub_add_eq_sub_sub, sub_eq_iff_eq_add, ← sub_smul] at hyz
  set t := c - (a + b)
  have h := C.add_mem hy' hz'
  rw [← hyz] at h
  rcases le_or_gt t 0 with ht | ht
  · set C' := C ⊔ span R {x}
    have hxC' : x ∈ C' := by
      simpa [C', mem_sup, mem_span_singleton] using ⟨0, by simp, 1, by simp⟩
    have hxC' : -t • x ∈ C' := C'.smul_mem (neg_nonneg.mpr ht) hxC'
    rw [neg_smul] at hxC'
    have hCC' : C ≤ C' := by simp [C']
    have hC : ∀ x ∈ C', -x ∈ C' → x = 0 := by -- this should actually be the definition of salient
      intro x hx hx'
      by_contra h
      exact hC _ hx h hx'
    have h0 := hC _ (hCC' h) hxC'
    rw [h0, Eq.comm, add_eq_zero_iff_eq_neg] at hyz
    rw [hyz] at hy'
    have h0' := hC _ (hCC' hz') (hCC' hy')
    simp [h0'] at hyz
    simp [hyz] at hy
    use a
  · rw [smul_mem_iff ht] at h
    contradiction

open Finset Submodule in
lemma exists_ray' {s : Finset M} (hs : ∃ x ∈ s, x ≠ 0) (hsal : (span R (s : Set M)).Salient) :
    ∃ x ∈ s, x ≠ 0 ∧ (span R {x}).IsFaceOf (span R s) := by classical
  induction s using Finset.induction with
  | empty => absurd hs; simp
  | insert w s hwr hind =>
    by_cases h : w ∈ span R s
    · by_cases hs' : ∃ x ∈ s, x ≠ 0
      · simp only [coe_insert, span, span_insert_eq_span h] at ⊢ hsal
        obtain ⟨x, hxs, hx⟩ := hind hs' hsal
        exact ⟨x, by simp [hxs, hx]⟩
      push_neg at hs'
      have hs' : ∀ x ∈ (s : Set M), x = 0 := fun x hx => hs' x hx
      simp only [Submodule.span_eq_bot.mpr hs', mem_bot] at h
      obtain ⟨x, hx, h⟩ := hs
      rcases mem_insert.mp hx with hx | hx
      · rw [hx] at h; contradiction
      · specialize hs' x hx; contradiction
    · use w
      simp_rw [← union_singleton, coe_union, span_union, coe_singleton, union_singleton,
        mem_insert, true_or, true_and] at ⊢ hsal
      exact ⟨by by_contra H; absurd h; simp [H],
        span_singleton_isFaceOf_sup_singleton_of_not_mem h hsal⟩

/-- A non-bottom salient FG cone has a ray face. -/
lemma FG.exists_ray (hfg : C.FG) (hC : C ≠ ⊥) (hsal : C.Salient) :
    ∃ x : M, x ≠ 0 ∧ (span R {x}).IsFaceOf C := by
  obtain ⟨s, rfl⟩ := hfg
  have h : ∃ x ∈ s, x ≠ 0 := by
    by_contra h
    simp [h] at hC
  obtain ⟨_, hx⟩ := exists_ray' h hsal
  exact ⟨_, hx.2⟩


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
