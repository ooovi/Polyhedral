import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.ModularLattice
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.SpanRank

import Polyhedral.Mathlib.Algebra.Module.Submodule.Restrict

namespace Submodule

open Function LinearMap Module

section Semiring

variable {M S R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

-- ## SPAN

-- Is this the better name?
protected alias span_gi := Submodule.gi

-- Q: Why does the following not exist?
-- instance {S : Submodule R M} : CoeOut (Submodule R S) (Submodule R M) := ⟨embed S⟩

alias le_span := subset_span

-- Q: should `Submodule.span_union` be a simp lemma? Yael says possibly
example (S S' : Set M) : span R (S ∪ S') = (span R S) ⊔ (span R S')
  := Submodule.span_union S S'

example (S S' : Submodule R M) : span R (S ∪ S') = S ⊔ S'
  := by simp

example (s t : Set M) : span R (s ∩ t) ≤ span R s :=
  span_mono inf_le_left

example (s t : Set M) : span R (s ∩ t) ≤ span R t :=
  span_mono inf_le_right

@[deprecated "this simplifies to the above examples" (since := "...")]
lemma span_inter_le (s t : Set M) : span R (s ∩ t) ≤ span R s ⊓ span R t :=
    le_inf (span_mono inf_le_left) (span_mono inf_le_right)


-- ## RESTRICT SCALARS

section RestrictedScalar

variable {S : Type*} [Semiring S] [Module S R] [Module S M] [IsScalarTower S R M]

open Function

variable (S)

lemma subtype_restrictScalars (p : Submodule R M) :
    p.subtype.restrictScalars S = (p.restrictScalars S).subtype := rfl

-- instance {p : Submodule R M} : CoeDep (Submodule R M) p (Submodule S M) := ⟨restrictScalars S p⟩


-- ## QUOTIENT

/- TODO: in general, when dealing with quotients there is no need to have the module we
  factor and the submodule we factor by over the same (semi)ring. It is then possible to
  have the module we factor over a semiring, while the submodule we factor by stays a
  ring, which is necessary for the existence of quotients. -/

variable {R : Type*} [Ring R]
variable {S : Type*} [Semiring S] [Module S R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M]

abbrev quot (S T : Submodule R M) := map T.mkQ S

/-- Restricted scalars version of `Submodule.range_mkQ`. -/
theorem range_mkQ' (p : Submodule R M) : range (p.mkQ.restrictScalars S) = ⊤ :=
  eq_top_iff'.2 <| by rintro ⟨x⟩; exact ⟨x, rfl⟩

#check range_mkQ
example (p : Submodule R M) : range p.mkQ = ⊤ := range_mkQ' p

/-- Restricted scalars version of `Submodule.ker_mkQ`. -/
@[simp]
theorem ker_mkQ' (p : Submodule R M) : ker (p.mkQ.restrictScalars S) = p.restrictScalars S :=
  by ext; simp

/-- Restricted scalars version of `Submodule.le_comap_mkQ`. -/
theorem le_comap_mkQ' {p : Submodule R M} (p' : Submodule S (M ⧸ p)) :
    p.restrictScalars S ≤ comap (p.mkQ.restrictScalars S) p' := by
  simpa using (comap_mono bot_le : ker (p.mkQ.restrictScalars S)
    ≤ comap (p.mkQ.restrictScalars S) p')

/-- Restricted scalars version of `Submodule.mkQ_map_self`. -/
@[simp] theorem mkQ_map_self' (p : Submodule R M) :
    map (p.mkQ.restrictScalars S) (p.restrictScalars S) = ⊥ := by
  rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkQ']

/-- Restricted scalars version of `Submodule.comap_map_mkQ`. -/
@[simp] theorem comap_map_mkQ' (p : Submodule R M) (p' : Submodule S M) :
    comap (p.mkQ.restrictScalars S) (map (p.mkQ.restrictScalars S) p')
      = p.restrictScalars S ⊔ p' := by simp [comap_map_eq, sup_comm]

#check comap_map_mkQ
example (p : Submodule R M) (p' : Submodule R M) :
  comap p.mkQ (map p.mkQ p') = p ⊔ p' := comap_map_mkQ p p'

/-- Restricted scalars version of `Submodule.comap_map_mkQ`. -/
@[simp] theorem map_comap_mkQ (p : Submodule R M) (p' : Submodule S (M ⧸ p)) :
    map (p.mkQ.restrictScalars S) (comap (p.mkQ.restrictScalars S) p') = p' := by
  simp [map_comap_eq, LinearMap.range_restrictScalars]

@[simp] lemma map_mkQ_le_iff_sup_le {p : Submodule R M} {s t : Submodule S M} :
    map (p.mkQ.restrictScalars S) s ≤ map (p.mkQ.restrictScalars S) t
      ↔ s ⊔ p.restrictScalars S ≤ t ⊔ p.restrictScalars S where
  mp h := by simpa [sup_comm] using comap_mono (f := p.mkQ.restrictScalars S) h
  mpr h := by simpa using map_mono (f := p.mkQ.restrictScalars S) h

@[simp] lemma map_mkQ_eq_iff_sup_eq {p : Submodule R M} {s t : Submodule S M} :
    map (p.mkQ.restrictScalars S) s = map (p.mkQ.restrictScalars S) t
      ↔ s ⊔ p.restrictScalars S = t ⊔ p.restrictScalars S where
  mp h := by simpa [sup_comm] using congrArg (comap <| p.mkQ.restrictScalars S) h
  mpr h := by simpa using congrArg (map <| p.mkQ.restrictScalars S) h

def mkQ_orderHom (p : Submodule R M) : Submodule S M →o Submodule S (M ⧸ p) where
  toFun := map (p.mkQ.restrictScalars S)
  monotone' := fun _ _ h => map_mono h

/-- `mkQ` as an order isomorphism between the submodules of M ⧸ p and the submodules of
  M that contain p. -/
def mkQ_orderIso (p : Submodule R M) : Set.Ici (p.restrictScalars S) ≃o Submodule S (M ⧸ p) where
  toFun s := s.1.map (p.mkQ.restrictScalars S)
  invFun s := ⟨s.comap (p.mkQ.restrictScalars S), le_comap_mkQ' s⟩
  left_inv s := by
    simp only [comap_map_mkQ']; congr
    exact (right_eq_sup.mpr (Set.mem_Ici.mp s.2)).symm
  right_inv s := by simp [map_comap_eq, range_mkQ']
  map_rel_iff' := by
    intro s t
    constructor
    · intro h
      replace h := comap_mono h (f := p.mkQ.restrictScalars S)
      simp only [Equiv.coe_fn_mk, comap_map_mkQ', sup_le_iff, le_sup_left, true_and] at h
      rw [← right_eq_sup.mpr t.2] at h
      exact h
    · exact (map_mono ·)

@[simp]
lemma mkQ_orderIso_apply {p : Submodule R M} (s : Set.Ici (p.restrictScalars S)) :
    p.mkQ_orderIso s = map (p.mkQ.restrictScalars S) s := rfl

@[simp]
lemma mkQ_orderIso_symm_apply {p : Submodule R M} (s : Submodule S (M ⧸ p)) :
    p.mkQ_orderIso.symm s = s.comap (p.mkQ.restrictScalars S) := rfl

lemma IsCompl.inf_eq_iff_sup_eq {p q : Submodule R M} {s t : Submodule S M} (hpq : IsCompl p q) :
    s ⊓ q.restrictScalars S = t ⊓ q.restrictScalars S
      ↔ s ⊔ p.restrictScalars S = t ⊔ p.restrictScalars S := by sorry

-- variable [HasRankNullity R] in
-- lemma exists_rank_le_codisjoint (S : Submodule R M) : ∃ T : Submodule R M,
--     Module.rank R T ≤ Module.rank R (⊤ : Submodule R (M ⧸ S)) ∧ Codisjoint S T := by
--   obtain ⟨s, hcard, hs⟩ := exists_set_linearIndependent R (M ⧸ S)
--   let inv := surjInv S.mkQ_surjective
--   use span R (inv '' s)
--   constructor
--   · rw[← hcard]
--     exact le_trans (spanRank_span_le_card _) Cardinal.mk_image_le
--   rw [codisjoint_iff, ← map_mkQ_eq_top]
--   ext x
--   simp only [mem_map, mem_top, iff_true]
--   have hx : x ∈ span R s := by simp only [hs, mem_top]
--   obtain ⟨n, f, g, rfl⟩ := mem_span_set'.mp hx
--   use ∑ i, f i • inv (g i)
--   constructor
--   · apply sum_mem
--     intro y _
--     refine smul_mem _ _ (mem_span_of_mem ?_)
--     simpa using ⟨g y, by simp⟩
--   · simp [inv, surjInv_eq S.mkQ_surjective]

/-- Replacement for `exists_isCompl` if `R` is not a Field. We can still always find a
  codisjoint submodule whose spanRank is equal the quotient's spanRank. -/
lemma exists_spanRank_codisjoint (S : Submodule R M) : ∃ T : Submodule R M,
    spanRank T = spanRank (⊤ : Submodule R (M ⧸ S)) ∧ Codisjoint S T := by
  obtain ⟨s, hcard, hs⟩ := (⊤ : Submodule R (M ⧸ S)).exists_span_set_card_eq_spanRank
  let inv := surjInv S.mkQ_surjective
  use span R (inv '' s)
  constructor
  · rw[← hcard]
    rw [le_antisymm_iff]
    constructor
    · exact le_trans (spanRank_span_le_card _) Cardinal.mk_image_le
    -- Function.injective_surjInv
    -- Submodule.spanRank_span_of_linearIndepOn
    -- Submodule.spanRank_span_le_card
    sorry
  rw [codisjoint_iff, ← map_mkQ_eq_top]
  ext x
  simp only [mem_map, mem_top, iff_true]
  have hx : x ∈ span R s := by simp only [hs, mem_top]
  obtain ⟨n, f, g, rfl⟩ := mem_span_set'.mp hx
  use ∑ i, f i • inv (g i)
  constructor
  · apply sum_mem
    intro y _
    refine smul_mem _ _ (mem_span_of_mem ?_)
    simpa using ⟨g y, by simp⟩
  · simp [inv, surjInv_eq S.mkQ_surjective]

/-- Replacement for `exists_isCompl` if `R` is not a Field. We can still always find a
  codisjoint submodule whose spanRank is at most the quotient's spanRank. -/
lemma exists_spanRank_le_codisjoint (S : Submodule R M) : ∃ T : Submodule R M,
    spanRank T ≤ spanRank (⊤ : Submodule R (M ⧸ S)) ∧ Codisjoint S T := by
  obtain ⟨s, hcard, hs⟩ := (⊤ : Submodule R (M ⧸ S)).exists_span_set_card_eq_spanRank
  let inv := surjInv S.mkQ_surjective
  use span R (inv '' s)
  constructor
  · rw[← hcard]
    exact le_trans (spanRank_span_le_card _) Cardinal.mk_image_le
  rw [codisjoint_iff, ← map_mkQ_eq_top]
  ext x
  simp only [mem_map, mem_top, iff_true]
  have hx : x ∈ span R s := by simp only [hs, mem_top]
  obtain ⟨n, f, g, rfl⟩ := mem_span_set'.mp hx
  use ∑ i, f i • inv (g i)
  constructor
  · apply sum_mem
    intro y _
    refine smul_mem _ _ (mem_span_of_mem ?_)
    simpa using ⟨g y, by simp⟩
  · simp [inv, surjInv_eq S.mkQ_surjective]



-- ## MODULAR

variable {R : Type*} [Ring R]
variable {S : Type*} [Semiring S] [Module S R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M]

-- TODO: quotientEquivOfIsCompl should not have explicit `p` and `q`

/-- Submodules over a ring are right modular in the lattice of submodules over a semiring.
  This is a version of `IsModularLattice.sup_inf_assoc_of_le` for the non-modular lattice
  of submodules over a semiring. -/
lemma sup_inf_assoc_of_le_restrictScalars {s : Submodule S M} (t : Submodule S M)
    {p : Submodule R M} (hsp : s ≤ p.restrictScalars S) :
    s ⊔ (t ⊓ p.restrictScalars S) = (s ⊔ t) ⊓ p.restrictScalars S := by
  ext x
  simp only [mem_sup, mem_inf, restrictScalars_mem]
  constructor
  · intro h
    obtain ⟨y, hy, z, ⟨hz, hz'⟩, hyzx⟩ := h
    refine ⟨⟨y, hy, z, hz, hyzx⟩, ?_⟩
    simpa [← hyzx] using p.add_mem (hsp hy) hz'
  · intro h
    obtain ⟨⟨y, hy, z, hz, hyzx⟩, hx⟩ := h
    refine ⟨y, hy, z, ⟨hz, ?_⟩, hyzx⟩
    rw [← add_right_inj (-y), neg_add_cancel_left] at hyzx
    rw [hyzx]
    specialize hsp hy
    rw [restrictScalars_mem, ← neg_mem_iff] at hsp
    exact p.add_mem hsp hx

/-- Submodules over a ring are left modular in the lattice of submodules over a semiring.
  This is a version of `IsModularLattice.inf_sup_assoc_of_le` for the non-modular lattice
  of submodules over a semiring. -/
lemma inf_sup_assoc_of_restrictScalars_le {s : Submodule S M} (t : Submodule S M)
    {p : Submodule R M} (hsp : p.restrictScalars S ≤ s) :
    s ⊓ (t ⊔ p.restrictScalars S) = (s ⊓ t) ⊔ p.restrictScalars S := by
  ext x
  simp only [mem_inf, mem_sup, restrictScalars_mem]
  constructor
  · intro h
    obtain ⟨hxs, y, hyt, z, hzp, hyzx⟩ := h
    use y
    constructor
    · refine ⟨?_, hyt⟩
      rw [← add_left_inj (-z), add_neg_cancel_right] at hyzx
      simpa [hyzx] using add_mem hxs <| hsp <| neg_mem (S := Submodule R M) hzp
    · use z
  · intro h
    obtain ⟨y, ⟨hys, hyt⟩, z, hzp, hyzx⟩ := h
    exact ⟨by simpa [← hyzx] using add_mem hys (hsp hzp), ⟨y, hyt, z, hzp, hyzx⟩⟩

/-- A version of `IsCompl.IicOrderIsoIci` for submodules with restricted scalars. -/
def IsCompl.IicOrderIsoIci_restrictScalars {p q : Submodule R M} (hpq : IsCompl p q) :
    Set.Iic (p.restrictScalars S) ≃o Set.Ici (q.restrictScalars S) where
  toFun s := ⟨s ⊔ q.restrictScalars S, by simp⟩
  invFun s := ⟨s ⊓ p.restrictScalars S, by simp⟩
  left_inv s := by
    simp [← sup_inf_assoc_of_le_restrictScalars _ s.2, ← restrictScalars_inf,
      disjoint_iff.mp hpq.symm.disjoint]
  right_inv s := by
    simp [← inf_sup_assoc_of_restrictScalars_le _ s.2, ← restrictScalars_sup,
      codisjoint_iff.mp hpq.codisjoint]
  map_rel_iff' := by
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, sup_le_iff, le_sup_right, and_true,
      Subtype.forall, Set.mem_Iic]
    intro s hs t ht
    constructor
    · intro h
      simpa [inf_eq_left.mpr hs, ← sup_inf_assoc_of_le_restrictScalars _ ht,
        ← restrictScalars_inf, inf_comm, disjoint_iff.mp hpq.disjoint]
        using inf_le_inf_right (p.restrictScalars S) h
    · exact (le_trans · le_sup_left)

-- Submodule.mapIic
-- orderIsoMapComap

noncomputable def IsCompl.foo {p q : Submodule R M} (hpq : IsCompl p q) :
    Submodule S (M ⧸ p) ≃o Submodule S q :=
  orderIsoMapComap <| (quotientEquivOfIsCompl _ _ hpq).restrictScalars S

def IsCompl.bar (p : Submodule R M) :
    Submodule S p ≃o Set.Iic (p.restrictScalars S) := Submodule.mapIic (p.restrictScalars S)

def quot_orderIso_Ici_restrictScalars (p : Submodule R M) :
    Submodule S (M ⧸ p) ≃o Set.Ici (p.restrictScalars S) where
  toFun q := ⟨comap (p.mkQ.restrictScalars S) q, le_comap_mkQ' q⟩
  invFun q := map (p.mkQ.restrictScalars S) q
  left_inv _ := by simp
  right_inv q := by
    have hq := q.2
    rw [Set.mem_Ici] at hq
    simp [hq]
  map_rel_iff' := by
    intro q r
    constructor <;> intro H
    · simpa using map_mono (f := p.mkQ.restrictScalars S) H
    · exact comap_mono H


section Experiment

variable {S R M N : Type*}
  [CommSemiring S] [CommRing R] [Algebra S R]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M]

-- I think this is not the best lemma. There should be something more fundamental about
-- quotients and IsCompl that should make this easy.
/-- The linear equivalence between `s / p` and `s ⊓ q`. -/
noncomputable def IsCompl.map_mkQ_equiv_inf {p q : Submodule R M} (hpq : IsCompl p q)
    {s : Submodule S M} (hps : p.restrictScalars S ≤ s) :
    map (p.mkQ : M →ₗ[S] M ⧸ p) s ≃ₗ[S] (s ⊓ q.restrictScalars S : Submodule S M) where
  toFun x := ⟨quotientEquivOfIsCompl _ _ hpq x, by
    obtain ⟨y, hys, hy⟩ := x.2; rw [← hy]
    obtain ⟨yp, yq, rfl, _⟩ := existsUnique_add_of_isCompl hpq y
    rw [← Submodule.quotientEquivOfIsCompl_apply_mk_coe _ _ hpq yq]
    simp only [quotientEquivOfIsCompl_apply_mk_coe, LinearMap.coe_restrictScalars, mkQ_apply,
      map_add, coe_add, mem_inf, restrictScalars_mem, (Quotient.mk_eq_zero p).mpr yp.2]
    simpa using add_mem (hps <| neg_mem (S := Submodule R M) yp.2) hys
  ⟩
  invFun x := ⟨p.mkQ x, x, by simpa using x.2.1⟩
  map_add' x y := by simp
  map_smul' r x := by simp [← algebraMap_smul R, map_smul]
  left_inv x := by simp
  right_inv x := by
    have H : (x : M) = (⟨x.1, x.2.2⟩ : q) := rfl
    ext; simp only [mkQ_apply]; rw [H]; congr
    exact Submodule.quotientEquivOfIsCompl_apply_mk_coe ..

noncomputable example {p q : Submodule R M} (hpq : IsCompl p q)
    {s : Submodule R M} (hps : p ≤ s) :
    map p.mkQ s ≃ₗ[R] (s ⊓ q : Submodule R M) := IsCompl.map_mkQ_equiv_inf hpq hps

end Experiment

end RestrictedScalar



-- -- ## QUOTIENTS

-- lemma mkQ_sup (S T : Submodule R M) :
--     (map S.mkQ T).mkQ ∘ S.mkQ = S.mkQ := sorry

-- lemma mkQ_sup (S T : Submodule R M) (hST : T ≤ S) :
--     (map S.mkQ T).mkQ ∘ S.mkQ = S.mkQ := sorry


-- -- ## LINEAR EQUIV

-- variable {R : Type*} [Semiring R]
-- variable {M : Type*} [AddCommMonoid M] [Module R M]
-- variable {N : Type*} [AddCommMonoid N] [Module R N]

-- structure LinearlyEquiv (s : Set M) (t : Set N) where
--   toFun : M →ₗ[R] N
--   toInv : N →ₗ[R] M
--   inv_fun : ∀ x ∈ s, toInv (toFun x) = x
--   fun_inv : ∀ x ∈ t, toFun (toInv x) = x

-- example (S : Submodule R M) (T : Submodule R N) : S ≃ₗ[R] T := sorry


end Semiring


section Ring

variable {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]

lemma IsCompl.projection_isProj {S T : Submodule R M} (hST : IsCompl S T) :
    IsProj S (IsCompl.projection hST) where
  map_mem := projection_apply_mem hST
  map_id x hx := projection_apply_left hST ⟨x, hx⟩

end Ring



section DivisionRing

open LinearMap

variable {M R : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]

lemma exists_isProj (S : Submodule R M) : ∃ p : M →ₗ[R] M, IsProj S p := by
  have ⟨_, hS'⟩ := exists_isCompl S
  exact ⟨_, IsCompl.projection_isProj hS'⟩

-- TODO: this should likely exist on modular lattices
lemma exists_le_disjoint_sup_self (S T : Submodule R M) :
    ∃ S' : Submodule R M, S' ≤ S ∧ Disjoint S' T ∧ S' ⊔ T = S ⊔ T := by
  obtain ⟨S', hSS', hST'⟩ := (codisjoint_restrict_sup S T).exists_isCompl
  exact ⟨embed S',
    by simpa [embed_restrict_of_le (toAddSubmonoid_le.mp hSS')] using embed_mono hSS',
    by simpa using embed_disjoint hST'.disjoint,
    by simpa using embed_codisjoint hST'.codisjoint⟩

lemma exists_extend {T S : Submodule R M} (hST : S ≤ T) :
    ∃ S' : Submodule R M, S' ⊔ T = ⊤ ∧ S' ⊓ T = S := by
  have ⟨T', ⟨hdis, hcod⟩⟩ := exists_isCompl T
  use T' ⊔ S
  rw [codisjoint_iff] at hcod
  rw [disjoint_iff] at hdis
  rw [sup_comm, ← sup_assoc, hcod, inf_comm, ← inf_sup_assoc_of_le, hdis]
  · simp
  · exact hST

-- lemma exists_extend' (T : Submodule R M) (S : Submodule R T) :
--     ∃ S' : Submodule R M, S' ⊔ T = ⊤ ∧ S'.restrict T = S := by
--   use exists_extend (T:=T) (S:=(S : Submodule R M)) (by sorry)
--   sorry

end DivisionRing

end Submodule
