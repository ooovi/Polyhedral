import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.ModularLattice
import Mathlib.RingTheory.Noetherian.Basic

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

@[simp] lemma span_union' (S S' : Submodule R M) : span R (S ∪ S') = S ⊔ S'
  := (Submodule.gi R M).l_sup_u S S'

-- span_sup'
example (S S' : Submodule R M) : span R (S ⊔ S' : Submodule R M) = S ⊔ S' := span_eq _

@[simp] lemma span_inter_le (s t : Set M) : span R (s ∩ t) ≤ span R s ⊓ span R t :=
    le_inf (span_mono Set.inter_subset_left) (span_mono Set.inter_subset_right)

@[simp] lemma span_inter (S S' : Submodule R M) : span R (S ∩ S') = S ⊓ S'
    := (Submodule.gi R M).l_inf_u S S'

alias span_inf := span_inter

lemma span_sSup (s : Set (Submodule R M)) :
    span R (sSup (SetLike.coe '' s)) = sSup s := (Submodule.gi R M).l_sSup_u_image s

lemma span_sInf (s : Set (Submodule R M)) :
    span R (sInf (SetLike.coe '' s)) = sInf s := (Submodule.gi R M).l_sInf_u_image s

lemma span_biUnion (s : Set (Submodule R M)) :
    span R (⋃ S ∈ s, S) = sSup s := by simpa using span_sSup s

lemma span_biInter (s : Set (Submodule R M)) :
    span R (⋂ S ∈ s, S) = sInf s := by simpa using span_sInf s

alias span_iInter := span_biInter


-- ## RESTRICT / EMBED

/- I suggest the alternative naming `restrict` for `submoduleOf` for the following reason:
  we want to have the same functionality on `PointedCone`, but there the name `submoduleOf`
  makes no sense. Using the same name is preferred for consistency.
  Not also that this cannot be an alias of `submoduleOf` because the argument are in the
  opposite order. This is in order to be consistent with `embed` for which the other order
  is not possible. This also allows us to view `restrict S` as the restriction operator.
-/

/-- The restriction of `S ⊓ T` reinterpreted as a submodule of `S`. -/
abbrev restrict (S T : Submodule R M) : Submodule R S := T.submoduleOf S -- T.comap S.subtype

-- Q: Shoud have `restrict` as an order hom? If yes, use the code below.
-- def restrict' (S : Submodule R M) : Submodule R M →o Submodule R S where
--   toFun := (submoduleOf · S)
--   monotone' := fun _ _ h _ => (h ·)

@[simp] lemma restrict_top (S : Submodule R M) : restrict S ⊤ = ⊤ := by
  simp only [submoduleOf, comap_top]
@[simp] lemma restrict_bot (S : Submodule R M) : restrict S ⊥ = ⊥ := by
  simp only [submoduleOf, comap_bot, ker_subtype]

lemma mem_restrict {S : Submodule R M} {T : Submodule R M} {x : S} (h : x ∈ restrict S T) :
    (x : M) ∈ T := by simpa using h

lemma mem_restrict_iff {S : Submodule R M} {T : Submodule R M} {x : S} :
    x ∈ restrict S T ↔ (x : M) ∈ T := by simp [submoduleOf]

@[simp] lemma restrict_self (S : Submodule R M) : restrict S S = ⊤ := submoduleOf_self S

lemma restrict_mono (S : Submodule R M) {T₁ T₂ : Submodule R M} (hCD : T₁ ≤ T₂) :
    restrict S T₁ ≤ restrict S T₂ := fun _ => (hCD ·)

lemma restrict_inf (S : Submodule R M) {T₁ T₂ : Submodule R M} :
    restrict S (T₁ ⊓ T₂) = (restrict S T₁) ⊓ (restrict S T₂)
  := by ext x; simp [restrict, submoduleOf]

lemma restrict_disjoint (U : Submodule R M) {S T : Submodule R M} (hST : Disjoint S T) :
    Disjoint (restrict U S) (restrict U T) := by
  rw [disjoint_iff] at *
  rw [← restrict_inf, hST, restrict_bot]

lemma codisjoint_restrict_sup (S T : Submodule R M) :
    Codisjoint (restrict (S ⊔ T) S) (restrict (S ⊔ T) T) := by
  rw [codisjoint_iff_exists_add_eq]
  intro x
  obtain ⟨y, hy, z, hz, h⟩ := mem_sup.mp x.2
  use ⟨y, mem_sup_left hy⟩
  use ⟨z, mem_sup_right hz⟩
  constructor
  · simp only [mem_restrict_iff, hy]
  constructor
  · simp only [mem_restrict_iff, hz]
  · simp only [AddMemClass.mk_add_mk, h]

example (S : Submodule R M) : Submodule R S ≃o Set.Iic S := Submodule.mapIic S

def restrict_equiv (S T : Submodule R M) : (S ⊓ T : Submodule R M) ≃ₗ[R] S.restrict T :=
  sorry

def restrict_orderHom (S : Submodule R M) : Submodule R M →o Submodule R S where
  toFun := restrict S
  monotone' _ _ := restrict_mono S

/-- A submodule `T` of a submodule `S` of `M` reintepreted as a submodule of `M`. -/
@[coe] abbrev embed {S : Submodule R M} (T : Submodule R S) : Submodule R M := T.map S.subtype

-- Q: Shoud have `embed` as an order embedding? If yes, use the code below.
-- def embed' {S : Submodule R M} : Submodule R S ↪o Submodule R M where
--   toFun := map S.subtype
--   inj' := map_injective_of_injective S.subtype_injective
--   map_rel_iff' := ⟨fun h x => by simpa using @h x, Submodule.map_mono⟩

@[simp] lemma mem_embed_iff {S : Submodule R M} {T : Submodule R S} {x : S} :
    (x : M) ∈ embed T ↔ x ∈ T := by simp

lemma mem_of_mem_embed {S : Submodule R M} {T : Submodule R S} {x : M} (hx : x ∈ embed T) :
    x ∈ S := by
  simp only [mem_map, subtype_apply, Subtype.exists, exists_and_right, exists_eq_right] at hx
  obtain ⟨hxS, _⟩ := hx
  exact hxS

abbrev of_mem_embed {S : Submodule R M} {T : Submodule R S} {x : M} (hx : x ∈ embed T) : S :=
  ⟨x, mem_of_mem_embed hx⟩

lemma of_mem_embed_mem {S : Submodule R M} {T : Submodule R S} {x : M} (hx : x ∈ embed T) :
    of_mem_embed hx ∈ T := by
  simp only [mem_map, subtype_apply, Subtype.exists, exists_and_right, exists_eq_right] at hx
  obtain ⟨_, h⟩ := hx
  exact h

@[simp] lemma embed_restrict (S T : Submodule R M) : embed (restrict S T) = S ⊓ T
  := map_comap_subtype _ _

lemma embed_restrict_of_le {S T : Submodule R M} (hST : T ≤ S) :
    embed (restrict S T) = T := by
  nth_rw 2 [← inf_eq_right.mpr hST]
  exact embed_restrict S T

@[simp] lemma restrict_embed {S : Submodule R M} (T : Submodule R S) : restrict S (embed T) = T
    := by ext x; simp [submoduleOf]

def restrict_surjective (S : Submodule R M) : Surjective (restrict S) := (⟨_, restrict_embed ·⟩)

lemma embed_injective {S : Submodule R M} : Injective (embed (S := S))
  := map_injective_of_injective S.subtype_injective

@[simp] lemma embed_inj {S : Submodule R M} {T₁ T₂ : Submodule R S} :
    embed T₁ = embed T₂ ↔ T₁ = T₂ := Injective.eq_iff embed_injective

lemma embed_mono {S : Submodule R M} {T₁ T₂ : Submodule R S} (hT : T₁ ≤ T₂) :
    embed T₁ ≤ embed T₂ := Submodule.map_mono hT

lemma embed_mono_rev {S : Submodule R M} {T₁ T₂ : Submodule R S} (hT : embed T₁ ≤ embed T₂) :
    T₁ ≤ T₂ := (by simpa using @hT ·)

@[simp] lemma embed_mono_iff {S : Submodule R M} {T₁ T₂ : Submodule R S} :
    embed T₁ ≤ embed T₂ ↔ T₁ ≤ T₂ where
  mp := embed_mono_rev
  mpr := embed_mono

@[simp] lemma embed_top {S : Submodule R M} : embed (⊤ : Submodule R S) = S := by simp
@[simp] lemma embed_bot {S : Submodule R M} : embed (⊥ : Submodule R S) = ⊥ := map_bot _

lemma embed_le {S : Submodule R M} (T : Submodule R S) : embed T ≤ S := by
  simpa using embed_mono le_top

lemma embed_sup {U : Submodule R M} (S T : Submodule R U) :
    embed (S ⊔ T) = embed S ⊔ embed T := map_sup ..

lemma embed_inf {U : Submodule R M} (S T : Submodule R U) :
    embed (S ⊓ T) = embed S ⊓ embed T := by
  ext x
  rw [mem_inf]
  constructor
  · intro h
    have h := of_mem_embed_mem h
    simp only [mem_inf, ← mem_embed_iff] at h
    exact h
  · intro h
    have h := And.intro (of_mem_embed_mem h.1) (of_mem_embed_mem h.2)
    rw [← mem_inf, ← mem_embed_iff] at h
    exact h

lemma embed_disjoint {U : Submodule R M} {S T : Submodule R U} (hST : Disjoint S T) :
    Disjoint (embed S) (embed T) := by
  rw [disjoint_def] at ⊢ hST
  intro x hxS hxT
  simpa using hST (of_mem_embed hxS) (of_mem_embed_mem hxS) (of_mem_embed_mem hxT)

lemma embed_disjoint_iff {U : Submodule R M} {S T : Submodule R U} :
    Disjoint S T ↔ Disjoint (embed S) (embed T) := by
  constructor
  · exact embed_disjoint
  intro hST
  rw [disjoint_def] at ⊢ hST
  intro x hxS hxT
  simpa using hST x (mem_embed_iff.mpr hxS) (mem_embed_iff.mpr hxT)

lemma embed_codisjoint {U : Submodule R M} {S T : Submodule R U} (hST : Codisjoint S T) :
    embed S ⊔ embed T = U := by rw [← embed_sup, codisjoint_iff.mp hST, embed_top]

def embed_equiv {S : Submodule R M} (T : Submodule R S) : T ≃ₗ[R] embed T where
  toFun x := ⟨S.subtype x, by simp⟩
  invFun x := ⟨⟨_, mem_of_mem_embed x.2⟩, mem_embed_iff.mp x.2⟩
  map_add' x y := by simp
  map_smul' r x := by simp
  left_inv x := by simp
  right_inv x := by simp

def embed_orderEmbed (S : Submodule R M) : Submodule R S ↪o Submodule R M where
  toFun := embed
  inj' := embed_injective
  map_rel_iff' := embed_mono_iff

def embed_CompleteLatticeHom (S : Submodule R M) :
    CompleteLatticeHom (Submodule R S) (Submodule R M) where
  toFun := embed
  map_sInf' := by
    intro s
    unfold embed
    sorry
  map_sSup' := by
    intro s
    unfold embed
    sorry

def embed_gi (S : Submodule R M) : GaloisCoinsertion (embed) (restrict S) where
  choice := fun T _ => restrict S T
  gc T U := by
    simp [← embed_mono_iff, embed_restrict, le_inf_iff, iff_and_self]
    exact fun _ => embed_le T
  u_l_le T := le_of_eq (restrict_embed T)
  choice_eq := by simp


-- ## RESTRICT SCALARS

section RestrictedScalar

variable {S : Type*} [Semiring S] [Module S R] [Module S M] [IsScalarTower S R M]

open Function

lemma restrictScalars_mono {s t : Submodule R M} (hST : s ≤ t) :
    s.restrictScalars S ≤ t.restrictScalars S := (restrictScalarsEmbedding S R M).monotone hST

@[simp] lemma restrictScalars_inf {s t : Submodule R M} :
    (s ⊓ t).restrictScalars S = (s.restrictScalars S) ⊓ (t.restrictScalars S) := by
  ext x; simp

@[simp] lemma restrictScalars_sup {s t : Submodule R M} :
    (s ⊔ t).restrictScalars S = (s.restrictScalars S) ⊔ (t.restrictScalars S):= by
  ext x; simp [mem_sup]

@[simp] lemma restrictScalars_sSup {s : Set (Submodule R M)} :
    (sSup s).restrictScalars S = sSup (restrictScalars S '' s) :=
  (restrictScalarsLatticeHom S R M).map_sSup' s

@[simp] lemma restrictScalars_sInf {s : Set (Submodule R M)} :
    (sInf s).restrictScalars S = sInf (restrictScalars S '' s) :=
  (restrictScalarsLatticeHom S R M).map_sInf' s


-- ## QUOTIENT

/- TODO: in general, when dealing with quotients there is no need to have the module we
  factor and the submodule we factor by over the same (semi)ring. It is then possible to
  have the module we factor over a semiring, while the submodule we factor by stays a
  ring, which is necessary for the existence of quotients. -/

variable {R : Type*} [Ring R]
variable {S : Type*} [Semiring S] [Module S R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M]

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
  map_smul' r x := by simp; sorry
  left_inv x := by simp
  right_inv x := by
    have H : (x : M) = (⟨x.1, x.2.2⟩ : q) := rfl
    ext; simp only [mkQ_apply]; rw [H]; congr
    exact Submodule.quotientEquivOfIsCompl_apply_mk_coe ..

noncomputable example {p q : Submodule R M} (hpq : IsCompl p q)
    {s : Submodule R M} (hps : p ≤ s) :
    map p.mkQ s ≃ₗ[R] (s ⊓ q : Submodule R M) := IsCompl.map_mkQ_equiv_inf hpq hps

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

/-- Disjoint submodules can be extended to complementary submodules. -/
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

lemma exists_le_disjoint_sup_self (S T : Submodule R M) :
    ∃ S' : Submodule R M, S' ≤ S ∧ Disjoint S' T ∧ S' ⊔ T = S ⊔ T := by
  obtain ⟨S', hSS', hST'⟩ := exists_isCompl_of_codisjoint (codisjoint_restrict_sup S T)
  exact ⟨embed S',
    by simpa [embed_restrict_of_le le_sup_left] using embed_mono hSS',
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
