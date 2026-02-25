import Mathlib.Order.Grade

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Exposed
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Ray

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


open Submodule in
/-- If a point `x` does not lie in a cone `C` but together with `C` spans a salient cone, then
  `x` spans a face of `span R (C ∪ {x})`. -/
lemma span_singleton_isFaceOf_sup_singleton_of_not_mem {C : PointedCone R M} {x : M}
    (hx : x ∉ C) (hC : (C ⊔ span R {x}).Salient) : (span R {x}).IsFaceOf (C ⊔ span R {x}) := by
  rw [isFaceOf_iff_mem_of_add_mem]
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


lemma bot_face (F : Face C) : F = ⊥ ↔ F.toPointedCone = ⊥ := sorry

lemma face_faces (h : F.IsFaceOf C) : F₁.IsFaceOf F ↔ F₁ ≤ F ∧ F₁.IsFaceOf C :=
  ⟨fun h' => ⟨h'.le, h'.trans h⟩,
   fun h' => ⟨h'.1, fun x y ha hs => h'.2.mem_of_smul_add_mem (h.le x) (h.le y) ha hs⟩⟩


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


theorem intervals (hfg : C.FG) (hsal : C.Salient) (G F : Face C) (hf : G ≤ F) :
    ∃ C' : PointedCone R M, Nonempty (Set.Icc G F ≃o Face C') := by
  wlog h : F = C
  · sorry
  · by_cases! h : G = ⊥
    · sorry
    ·
      have hgfg : G.FG := IsFaceOf.fg_of_fg hfg G.isFaceOf
      have hgsal : G.toPointedCone.Salient := hsal.anti G.isFaceOf.le
      obtain ⟨v, hv0, hvray⟩ := FG.exists_ray hgfg (fun n => h ((bot_face G).mpr n)) hgsal
      have := (face_faces G.isFaceOf).mp hvray
      obtain ⟨s, hs⟩ := hfg
      sorry

/-- A face of a pointed cone `C` that is supported by a hyperplane consists of all points in the
intersection of its linear span and `C`. -/
lemma cone_eq_inter_span (C : PointedCone R M) (G : Face C) {ρ : M →ₗ[R] R}
    (hρG : ∀ x ∈ C, ρ x = 0 ↔ x ∈ G) :
    (G : Set M) = (Submodule.span R (G : Set M) : Set M) ∩ (C : Set M) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_inter_iff]
  constructor
  · intro hx
    simpa [Submodule.mem_span] using ⟨fun p hp => p.mem_toAddSubgroup.mp (hp hx), G.isFaceOf.le hx⟩
  · intro ⟨hspan, hC⟩
    apply (hρG _ hC).mp
    have : ρ.domRestrict (Submodule.span R ↑G) ⟨x, hspan⟩ = 0 := by
      have := (Submodule.linearMap_eq_zero_iff_of_eq_span (S := (G : Set M)) (ρ.domRestrict _) rfl)
      rw [this.mpr (fun s => (hρG _ (G.isFaceOf.le s.prop)).mpr s.prop)]
      exact LinearMap.zero_apply _
    exact LinearMap.mem_ker.mp this

lemma finrank_strictMono_of_fg {C : PointedCone R M} (hCfg : C.FG) :
    StrictMono (fun F : Face C => (F : PointedCone R M).finrank) := by
  intro F G hFG
  obtain ⟨_, _, hφF⟩ := IsFaceOf.FG.exposed hCfg F.isFaceOf
  obtain ⟨_, _, hρG⟩ := IsFaceOf.FG.exposed hCfg G.isFaceOf
  letI : FiniteDimensional R G.toPointedCone.linSpan := by
    refine (Submodule.fg_iff_finiteDimensional _).mp ?_
    obtain ⟨_, hgfg⟩ : G.FG := G.isFaceOf.fg_of_fg hCfg
    simpa [← hgfg] using Submodule.FG.of_finite
  apply Submodule.finrank_lt_finrank_of_lt
  have sb : (F : Set M) < (G : Set M) := HasSSubset.SSubset.lt hFG
  rw [cone_eq_inter_span C F hφF, cone_eq_inter_span C G hρG] at sb
  change (Submodule.span R (F : Set M) : Set M) ⊂ Submodule.span R (G : Set M)
  apply ssubset_of_subset_of_ne <| Submodule.span_mono (R := R) hFG.le
  intro h
  rw [h] at sb
  exact irrefl _ sb

lemma finrank_quot_add_finrank_of_fg {C : PointedCone R M} {F G : Face C}
    (hFG : F ≤ G) (hGfg : (G : PointedCone R M).FG) :
    (PointedCone.quot (G : PointedCone R M) ((F : PointedCone R M).linSpan)).finrank
      + (F : PointedCone R M).finrank
      = (G : PointedCone R M).finrank := by sorry

lemma finrank_covBy_of_fg {C : PointedCone R M} (hCfg : C.FG)
    {F G : Face C} (hFG : F ⋖ G) :
    (F : PointedCone R M).finrank ⋖ (G : PointedCone R M).finrank := by sorry

/-- The face lattice of a finitely generated cone is graded by face dimension. -/
noncomputable instance gradeOrder_finrank_of_fg {C : PointedCone R M}
    (hCfg : C.FG) : GradeOrder ℕ (Face C) where
  grade F := (F : PointedCone R M).finrank
  grade_strictMono := finrank_strictMono_of_fg hCfg
  covBy_grade := fun {_ _} hFG => finrank_covBy_of_fg hCfg hFG






lemma Face.rank_one_of_atom (hfg : C.FG) (hsal : C.Salient)
    (F : Face C) (hF : IsAtom F) : F.rank = 1 := by
  by_cases! h : F.rank < 1
  · absurd (Face.bot_iff_rank_zero hsal).mp <| Cardinal.lt_one_iff_zero.mp h
    exact hF.ne_bot
  have h1 : (F : PointedCone R M).FG := IsFaceOf.fg_of_fg hfg F.isFaceOf
  have h2 : (F : PointedCone R M).Salient := IsFaceOf.salient hsal F.isFaceOf
  obtain ⟨x, hx0, hxF⟩ := by
    refine FG.exists_ray h1 (fun h3 ↦ ?_) h2
    replace h : (F : PointedCone R M).rank ≥ 1 := h
    simp [(F : PointedCone R M).bot_iff_rank_zero.mpr h3] at h
  let test : Face C := ⟨PointedCone.span R {x}, hxF.trans F.isFaceOf⟩
  have t_rank : test.rank = 1 := rank_one_of_ray hx0
  have : test ≤ F := hxF.le
  rcases (IsAtom.le_iff hF).1 this with h | h
  · rw [(bot_iff_rank_zero hsal).2 h] at t_rank
    simp at t_rank
  rw [← h, t_rank]


end PointedCone
