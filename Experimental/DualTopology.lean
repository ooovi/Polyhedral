import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.LinearAlgebra.BilinearMap

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual

namespace PointedCone

open Module Function
open Filter
open Topology

variable {α 𝕜 𝕝 E F : Type*}

section DualTopology

/-- The space `E` equipped with the weak topology induced by the bilinear form `p`. -/
@[nolint unusedArguments]
def DualTop [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (_ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) := E
deriving AddCommMonoid, Module 𝕜

namespace DualTop

instance instAddCommGroup [CommSemiring 𝕜] [a : AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (p : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommGroup (DualTop p) := a

instance (priority := 100) instModule' [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E]
    [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [m : Module 𝕝 E] (p : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    Module 𝕝 (DualTop p) := m

instance instIsScalarTower [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [s : IsScalarTower 𝕝 𝕜 E]
    (p : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (DualTop p) := s

section Semiring

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

instance instTopologicalSpace : TopologicalSpace (DualTop p) :=
  TopologicalSpace.generateFrom {s : Set M | dual p.flip (dual p sᶜ) = sᶜ}

----------

/-- The coercion `(fun x y => p x y) : E → (F → 𝕜)` is continuous. -/
theorem coeFn_continuous : Continuous fun (x : DualTop p) y => p x y :=
  continuous_induced_dom

@[fun_prop]
theorem eval_continuous (y : F) : Continuous fun x : DualTop p => p x y :=
  (continuous_pi_iff.mp (coeFn_continuous p)) y

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → DualTop p}
    (h : ∀ y, Continuous fun a => p (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

/-- The coercion `(fun x y => p x y) : E → (F → 𝕜)` is an embedding. -/
theorem isEmbedding {p : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : Function.Injective p) :
    IsEmbedding fun (x : DualTop p) y => p x y :=
  Function.Injective.isEmbedding_induced <| LinearMap.coe_injective.comp hB

theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α → DualTop p} {x : DualTop p}
    (hB : Function.Injective p) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => p (f i) y) l (𝓝 (p x y)) := by
  rw [← tendsto_pi_nhds, (isEmbedding hB).tendsto_nhds_iff]
  rfl

/-- Addition in `DualTop p` is continuous. -/
instance instContinuousAdd [ContinuousAdd 𝕜] : ContinuousAdd (DualTop p) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine
    cast (congr_arg _ ?_)
      (((coeFn_continuous p).comp continuous_fst).add ((coeFn_continuous p).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.add_apply, map_add, LinearMap.add_apply]

/-- Scalar multiplication by `𝕜` on `DualTop p` is continuous. -/
instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (DualTop p) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine cast (congr_arg _ ?_) (continuous_fst.smul ((coeFn_continuous p).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.smul_apply, LinearMap.map_smulₛₗ, RingHom.id_apply,
    LinearMap.smul_apply]

/--
Map `F` into the topological dual of `E` with the weak topology induced by `F`
-/
def eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] :
    F →ₗ[𝕜] StrongDual 𝕜 (DualTop p) where
  toFun f := ⟨p.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

end Semiring

section Ring

variable [TopologicalSpace 𝕜] [CommRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]


variable (p : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- `DualTop p` is a `IsTopologicalAddGroup`, meaning that addition and negation are
continuous. -/
instance instIsTopologicalAddGroup [ContinuousAdd 𝕜] : IsTopologicalAddGroup (DualTop p) where
  toContinuousAdd := by infer_instance
  continuous_neg := by
    refine continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => ?_)
    refine cast (congr_arg _ ?_) (eval_continuous p (-y))
    ext x
    simp only [map_neg, Function.comp_apply, LinearMap.neg_apply]

end Ring

end DualTop

end WeakTopology

end PointedCone
