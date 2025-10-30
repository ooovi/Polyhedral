-- /-
-- Copyright (c) 2025 Martin Winter. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Martin Winter
-- -/
-- import Mathlib.LinearAlgebra.Dual.Defs
-- import Mathlib.LinearAlgebra.PerfectPairing.Basic
-- import Mathlib.RingTheory.Finiteness.Basic

-- import Polyhedral.Halfspace

-- /-!
-- # Polyhedral cones
-- ...
-- -/

-- open Function Module

-- variable {𝕜 M N : Type*}

-- variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
--   [AddCommGroup M] [Module 𝕜 M] [Module.Finite 𝕜 M]
--   [AddCommGroup N] [Module 𝕜 N] [Module.Finite 𝕜 N]

-- namespace PointedCone

-- -- This is extreme face
-- def IsFaceOf' (F C : PointedCone 𝕜 M)
--   := ∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Set.Icc 0 1, t • x  + (1 - t) • y ∈ F → (x ∈ F ∧ y ∈ F)

-- -- This is exposed face
-- def IsFaceOf (F C : PointedCone 𝕜 M)
--   := ∃ H : HalfspaceOrTop 𝕜 M, C ≤ H ∧ C ⊓ H.boundary = F

-- lemma IsFaceOf.trans {C₁ C₂ C₃ : PointedCone 𝕜 M} (h12 : C₂.IsFaceOf C₁) (h23 : C₃.IsFaceOf C₂) :
--   C₃.IsFaceOf C₁ := sorry

-- lemma IsFaceOf.le {F C : PointedCone 𝕜 M} (hF : F.IsFaceOf C) : F ≤ C := sorry

-- omit [Module.Finite 𝕜 M] in
-- lemma IsFaceOf.self (C : PointedCone 𝕜 M) : C.IsFaceOf C := ⟨⊤, by simp⟩

-- lemma IsFaceOf.lineal (C : PointedCone 𝕜 M) : IsFaceOf C.lineal C := by
--   by_cases C.lineal ≥ C
--   case pos h => rw [le_antisymm (PointedCone.lineal_le C) h]; exact self C
--   case neg h =>
--     simp at h
--     obtain ⟨x, hx⟩ := Set.not_subset_iff_exists_mem_notMem.mp h
--     -- use .of_dual_pt x -- DANG, need x from the dual space
--     sorry

-- lemma IsFaceOf.inf {C F₁ F₂ : PointedCone 𝕜 M} (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
--     (F₁ ⊓ F₂).IsFaceOf C := by
--   obtain ⟨⟨S₁, ⟨x₁, rfl⟩⟩, hCH₁, rfl⟩ := h₁
--   obtain ⟨⟨S₂, ⟨x₂, rfl⟩⟩, hCH₂, rfl⟩ := h₂
--   use .of_dual_pt (x₁ + x₂)
--   constructor
--   · rw [← SetLike.coe_subset_coe, Set.subset_def] at *
--     intro x hx
--     simp at *
--     have h := add_le_add (hCH₁ x hx) (hCH₂ x hx)
--     rw [add_zero] at h
--     exact h
--   · ext x
--     simp [HalfspaceOrTop.boundary, PointedCone.lineal_mem]
--     constructor
--     · intro h
--       specialize hCH₁ h.1
--       specialize hCH₂ h.1
--       simp at *
--       sorry
--     · intro h
--       specialize hCH₁ h.1.1
--       specialize hCH₂ h.1.1
--       simp at *
--       sorry

-- -- TODO: the subdual strategy for taking the sup of faces only works for polyhedral cones

-- variable (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair] in
-- def subdual (C F : PointedCone 𝕜 M) : PointedCone 𝕜 N := dual p F ⊓ dual p C

-- variable (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair] in
-- lemma IsFaceOf.subdual_dual {C F : PointedCone 𝕜 M} (hF : F.IsFaceOf C) :
--     (subdual p C F).IsFaceOf (dual p C) := by
--   sorry

-- lemma IsFaceOf.sup {C F₁ F₂ : PointedCone 𝕜 M} (h1 : F₁.IsFaceOf C) (h2 : F₂.IsFaceOf C) :
--     (subdual .id (dual (Dual.eval 𝕜 M) C)
--       ((subdual (Dual.eval 𝕜 M) C F₁) ⊓ (subdual (Dual.eval 𝕜 M) C F₂))).IsFaceOf C := by
--   sorry

-- lemma IsFaceOf.sSup {C : PointedCone 𝕜 M} {Fs : Set (PointedCone 𝕜 M)}
--     (hFs : ∀ F ∈ Fs, F.IsFaceOf C) : (sSup Fs).IsFaceOf C := by
--   sorry

-- -- lemma IsFaceOf.sup' {C F₁ F₂ : PointedCone 𝕜 M} (h1 : F₁.IsFaceOf C) (h2 : F₂.IsFaceOf C) :
-- --     (sSup {F : PointedCone 𝕜 M | F.IsFaceOf C ∧ F₁ ≤ F ∧ F₂ ≤ F}).IsFaceOf C := by
-- --   sorry

-- structure Face (C : PointedCone 𝕜 M) extends PointedCone 𝕜 M where
--   isFaceOf : IsFaceOf toSubmodule C

-- def of_isFaceOf {F C : PointedCone 𝕜 M} (hF : F.IsFaceOf C) : Face C := ⟨F, hF⟩

-- instance (C : PointedCone 𝕜 M) : Bot (Face C) := ⟨of_isFaceOf <| IsFaceOf.lineal C⟩
-- instance (C : PointedCone 𝕜 M) : Top (Face C) := ⟨of_isFaceOf <| IsFaceOf.self C⟩

-- instance (C : PointedCone 𝕜 M) : Min (Face C) where
--   min F₁ F₂ := of_isFaceOf <| IsFaceOf.inf F₁.isFaceOf F₂.isFaceOf

-- variable (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) [p.IsPerfPair] in
-- instance (C : PointedCone 𝕜 M) : Max (Face C) where
--   max F₁ F₂ := of_isFaceOf <| IsFaceOf.sup F₁.isFaceOf F₂.isFaceOf

-- -- instance {C : PolyhedralCone 𝕜 M} : Coe (Face C) (PolyhedralCone 𝕜 M) := sorry

-- end PointedCone


























-- import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Polyhedral
-- import Mathlib.LinearAlgebra.PerfectPairing.Basic
-- import Mathlib.LinearAlgebra.Span.Defs
-- import Mathlib.Algebra.Module.LinearMap.Defs
-- import Mathlib.LinearAlgebra.PerfectPairing.Basic


-- lemma ex_imp_of_imp_ex {α : Type*} [hα : Nonempty α] {P : Prop} {Q : α → Prop} :
--     (P → ∃ x, Q x) → ∃ x, P → Q x := by
--   intro h
--   by_cases hP : P
--   · tauto
--   · use Classical.choice hα
--     tauto

-- theorem Finset.exists_le'
--     {α β : Type*} [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)] [DecidableEq β]
--     (s : Finset α) (f : α → β) : ∃ M, ∀ i ∈ s, f i ≤ M := by
--   let ⟨M, hM⟩ := Finset.exists_le (image f s)
--   use M
--   simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hM
--   assumption

-- theorem Finset.exists_lt'
--     {α β : Type*} [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)] [NoMaxOrder β] [DecidableEq β]
--     (s : Finset α) (f : α → β) : ∃ M, ∀ i ∈ s, f i < M := by
--   obtain ⟨M, hM⟩ := Finset.exists_le' s f
--   obtain ⟨N, hN⟩ := exists_gt M
--   use N
--   exact fun i hi => lt_of_le_of_lt (hM i hi) hN

-- theorem eq_zero_of_nonneg_add
--     {α : Type*} [AddGroup α] [PartialOrder α] [AddLeftMono α] {a b : α} :
--     0 ≤ a → 0 ≤ b → a + b = 0 → a = 0 ∧ b = 0 := fun ha hb hab => by
--   constructor
--   · apply eq_neg_of_add_eq_zero_right at hab
--     rw [hab, Left.nonneg_neg_iff] at hb
--     exact le_antisymm hb ha
--   · apply eq_neg_of_add_eq_zero_left at hab
--     rw [hab, Left.nonneg_neg_iff] at ha
--     exact le_antisymm ha hb

-- theorem span_inter_le {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (s t : Set M) :
--   Submodule.span R (s ∩ t) ≤ Submodule.span R s ⊓ Submodule.span R t := by
--   rw [le_inf_iff]
--   constructor <;> apply Submodule.span_mono
--   · exact Set.inter_subset_left
--   · exact Set.inter_subset_right



-- open Submodule Pointwise LinearMap

-- namespace PointedCone

-- variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
--   [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

-- variable (p) in
-- def perp (u : M) : PointedCone R N where
--     carrier := {v | p u v = 0}
--     add_mem' {v v'} hv hv' := by simp [Set.mem_setOf_eq ▸ hv, Set.mem_setOf_eq ▸ hv']
--     zero_mem' := by simp
--     smul_mem' c {v} hv := by simp [Set.mem_setOf_eq ▸ hv]

-- @[simp] lemma mem_perp {u : M} {v : N} : v ∈ perp p u ↔ p u v = 0 := by simp [perp, comm]
-- @[simp] lemma perp_zero : perp p 0 = ⊤ := by ext; simp
-- lemma neg_perp {u : M} : perp p u = perp (-p) u := by ext; simp [perp, comm]
-- lemma perp_dual {u : M} : perp p u ≤ dual LinearMap.id {p u} := by simp +contextual [perp, dual]

-- variable (p) in
-- def IsFace (c : PointedCone R N) (f : PointedCone R N) : Prop :=
--   ∃ u ∈ dual p.flip c, f = c ⊓ perp p u

-- lemma isFace_subset {c : PointedCone R N} {f : PointedCone R N} (h : IsFace p c f) : f ≤ c := by
--   obtain ⟨h₁, ⟨h₂, h₃⟩⟩ := h
--   simp [h₃]

-- theorem isFace_polyhedral
--     {c : PointedCone R N} (hc : IsPolyhedral c)
--     {f : PointedCone R N} (hf : IsFace p c f) : IsPolyhedral f := by
--   obtain ⟨S, hS₁, hS₂⟩ := hc
--   obtain ⟨u, hu₁, hu₂⟩ := hf
--   subst hS₂
--   subst hu₂
--   use (insert (-(p u)) S)
--   simp only [hS₁.insert, dual_insert, true_and]
--   ext
--   simp only [mem_inf, mem_dual, Set.mem_singleton_iff, id_coe, id_eq, forall_eq, neg_apply,
--     Left.nonneg_neg_iff, and_comm, and_congr_left_iff]
--   intro a
--   specialize hu₁ a
--   rw [flip_apply] at hu₁
--   exact ⟨fun b => le_antisymm_iff.mpr ⟨b, hu₁⟩, le_of_eq⟩

-- theorem isFace_intersection
--     {c : PointedCone R N}
--     {f : PointedCone R N} (hf : IsFace p c f)
--     {f' : PointedCone R N} (hf' : IsFace p c f') :
--     IsFace p c (f ⊓ f') := by
--   obtain ⟨u, hu₁, hu₂⟩ := hf
--   subst hu₂
--   obtain ⟨u', hu'₁, hu'₂⟩ := hf'
--   subst hu'₂
--   use u + u'
--   apply And.intro (add_mem hu₁ hu'₁)
--   ext v
--   constructor
--   · intro hv
--     obtain ⟨⟨hv₁, hv₂⟩, ⟨-, hv₃⟩⟩ := hv
--     apply And.intro hv₁
--     rw [SetLike.mem_coe, mem_perp] at hv₂ hv₃
--     simp [hv₂, hv₃]
--   · intro ⟨hv₁, hv₂⟩
--     rw [SetLike.mem_coe] at hv₁ hv₂
--     specialize hu₁ hv₁
--     specialize hu'₁ hv₁
--     rw [LinearMap.flip_apply] at hu₁ hu'₁
--     rw [mem_perp, map_add, LinearMap.add_apply] at hv₂
--     obtain ⟨huv, hu'v⟩ := eq_zero_of_nonneg_add hu₁ hu'₁ hv₂
--     trivial

-- theorem add_mem_face
--     {c : PointedCone R N}
--     {f : PointedCone R N} (hf : IsFace p c f)
--     {v : N} {hv : v ∈ c} {w : N} {hw : w ∈ c} :
--     v + w ∈ f → v ∈ f ∧ w ∈ f := fun h => by
--   obtain ⟨u, hu₁, hu₂⟩ := hf
--   subst hu₂
--   obtain ⟨h₁, h₂⟩ := h
--   rw [SetLike.mem_coe, mem_perp, map_add] at h₂
--   have ⟨huv, huw⟩ := eq_zero_of_nonneg_add (hu₁ hv) (hu₁ hw) h₂
--   simp only [mem_inf]
--   trivial

-- lemma isFace_inter_span {c : PointedCone R N}
--     {f : PointedCone R N} (hf : IsFace p c f) :
--     f = (span R f) ⊓ c := by
--   simp [isFace_subset hf]




-- -- -- NoZeroSMulDivisors ok?
-- -- lemma span_perpSpace_inf [NoZeroSMulDivisors { c : R // 0 ≤ c } R] {S : Set N} {u : M}
-- --     (d : u ∈ dual p.flip S) :
-- --     span R S ⊓ PerpSpace p {u} = span R (S ∩ PerpSpace p {u}) := by
-- --   apply eq_of_le_of_ge
-- --   · simp [LE.le, PerpSpace]
-- --     intros x a xp
-- --     induction' a using span_induction with a b c d e f g h i j k l
-- --     · exact mem_span_of_mem (Set.mem_inter b xp)
-- --     · simp
-- --     · --simp [map_add] at xp
-- --       have : c + d ∈ span R S := Submodule.add_mem _ e f
-- --       have : c + d ∈ PerpSpace p {u} := by simp [PerpSpace, xp]

-- --       simp [mem_span]
-- --       intros

-- --       sorry
-- --     -- apply Set.mem_of_subset_of_mem sub
-- --     -- simp [xp]
-- --     -- have := mem_dual.mp d
-- --     -- simp [flip_apply] at this
-- --     -- have : S ⊆ {v | (p u) v = 0} := by intro a a0; simp;
-- --     · simp only [map_smul_of_tower, smul_eq_zero] at xp
-- --       cases h : xp with
-- --       | inl a => simp [a]
-- --       | inr a => exact Submodule.smul_mem _ _ (l a)
-- --   · apply le_trans (span_inter_le _ _)
-- --     simp

-- -- end Definitons

-- section LinearOrder

-- variable {R M N : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
--   [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

-- theorem face_face (hR : ∀ (x y : R), 0 < y → ∃ z, 0 < z * y + x)
--     {c : PointedCone R N} (hc : c.FG)
--     {f : PointedCone R N} (hf : IsFace p c f)
--     {f' : PointedCone R N} (hf' : IsFace p f f') :
--     IsFace p c f' := by
--   obtain ⟨u, hu₁, hu₂⟩ := hf
--   subst hu₂
--   obtain ⟨u', hu'₁, hu'₂⟩ := hf'
--   subst hu'₂
--   obtain ⟨S, hS⟩ := hc
--   have hSc : ∀ v ∈ S, v ∈ c := fun v hv => hS ▸ subset_span hv
--   obtain h_for_ex : ∀ v ∈ S, 0 < p u v → ∃ r : R, 0 < p (r • u + u') v := by
--     intro v hv huv
--     obtain ⟨n, hn⟩ := hR (p u' v) (p u v) huv
--     use n
--     simpa
--   obtain ⟨rf, hrf⟩ : ∃ (r : N → R), ∀ v ∈ S, 0 < p u v → 0 < p (r v • u + u') v := by
--     apply Classical.axiomOfChoice (r := fun v r => _ → _ → 0 < p (r • u + u') v)
--     exact fun _ => ex_imp_of_imp_ex (fun hv => ex_imp_of_imp_ex (h_for_ex _ hv))
--   obtain ⟨r, hr⟩ := Finset.exists_le' S rf
--   have HS : ∀ v ∈ S, 0 ≤ p (r • u + u') v ∧
--       (p (r • u + u') v = 0 ↔ p u v = 0 ∧ p u' v = 0) := fun v hv => by
--     have huv : 0 ≤ p u v := hu₁ (hSc _ hv)
--     rcases lt_or_eq_of_le huv with huv₁ | huv₂
--     · have H : 0 < (p (r • u + u')) v := by
--         apply lt_of_lt_of_le (hrf _ hv huv₁)
--         simp [huv₁, hv, hr]
--       apply And.intro (le_of_lt H)
--       constructor <;> aesop
--     · have hu'v : 0 ≤ p u' v := hu'₁ (by simp; exact ⟨hSc _ hv, huv₂.symm⟩)
--       simp [←huv₂, hu'v]
--   have H : ∀ v ∈ c, 0 ≤ p (r • u + u') v ∧
--       (p (r • u + u') v = 0 ↔ p u v = 0 ∧ p u' v = 0) := fun v hv => by
--     rw [iff_def, ←and_assoc]
--     apply And.intro _ (by rintro ⟨huv, hu'v⟩; simp [huv, hu'v])
--     obtain ⟨l, hl, hlv⟩ := Submodule.mem_span_finset.mp (hS ▸ hv)
--     simp_rw [←Nonneg.coe_smul] at hlv
--     subst hlv
--     simp_rw [map_sum, map_smul_of_tower]
--     have hnn := fun w hw => smul_nonneg (l w).2 (HS w hw).1
--     apply And.intro (Finset.sum_nonneg hnn)
--     intro H
--     have h_ruu'_zero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp H
--     simp_rw [smul_eq_zero] at h_ruu'_zero
--     have h_or_zero := fun i hi => Or.imp_right (HS i hi).2.mp (h_ruu'_zero i hi)
--     simp_rw [or_and_left] at h_or_zero
--     have hu_zero := fun i hi => smul_eq_zero.mpr (h_or_zero i hi).1
--     have hu'_zero := fun i hi => smul_eq_zero.mpr (h_or_zero i hi).2
--     constructor <;> apply Finset.sum_eq_zero <;> assumption
--   use r • u + u'
--   constructor
--   · apply fun v hv => (H v hv).1
--   · ext v
--     simp_rw [mem_inf, mem_perp]
--     have := fun hv => (H v hv).2
--     tauto

-- end LinearOrder

-- end PointedCone


-- -- open PointedCone


-- -- section Definition

-- -- variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
-- --   {N : Type*} [AddCommGroup N] [Module R N] {p : N →ₗ[R] N →ₗ[R] R}



-- -- namespace PolyhedralCone

-- -- attribute [coe] toSubmodule

-- -- instance : CoeOut (PolyhedralCone R N) (PointedCone R N) := ⟨toSubmodule⟩
-- -- instance : Coe (PolyhedralCone R N) (PointedCone R N) := ⟨toSubmodule⟩

-- -- @[ext]
-- -- theorem ext {c c' : PolyhedralCone R N} (h : (c : PointedCone R N) = c') : c = c' :=
-- --   by cases c; cases c'; congr

-- -- instance : SetLike (PolyhedralCone R N) N where
-- --   coe s := s.carrier
-- --   coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h


-- -- -- TODO is this the most general M?
-- -- instance : LE (PolyhedralCone R N) := {le := fun f f' => IsFace (M := Module.Dual R N) .id f f'}



-- -- end PolyhedralCone

-- -- end Definition


-- -- namespace PolyhedralCone

-- -- variable {𝕜 N : Type*}
-- --   [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
-- --   [AddCommGroup N] [Module 𝕜 N] [Module.Finite 𝕜 N]

-- -- instance : PartialOrder (PolyhedralCone 𝕜 N) := {
-- --   le_refl := by intro a; use 0; constructor <;> simp
-- --   lt := fun a b => a ≤ b ∧ ¬ b ≤ a
-- --   le_trans := fun a b c ha hb => by {
-- --     have hR : ∀ (x y : 𝕜), 0 < y → ∃ z, 0 < z * y + x := fun x y hy => by
-- --       use - (x - 1) / y
-- --       field_simp
-- --       simp
-- --     exact face_face hR (fg_of_isPolyhedral a.isPolyhedral) ha hb
-- --   }
-- --   le_antisymm := fun a b hab hba => ext (antisymm (isFace_subset hba) (isFace_subset hab))
-- -- }

-- -- abbrev IsFacet (a b : PolyhedralCone 𝕜 N) := a ⋖ b

-- -- end PolyhedralCone
