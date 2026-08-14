
# Polyhedral theory for mathlib

The goal of this project is to build a flexible, general and useful implementation of polyhedral geometry/combinatorics in Lean, for mathlib, on which more advanced theory can be built. This repository serves as a testing ground for features from which we subsequently build PRs for mathlib.

The main discussion happens on Zulip, in particular, in the thread ["Polyhedra in mathlib"](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Polyhedra.20in.20mathlib/with/579450695).

Currently the project implements:
* duals of finitely generated cones (H-cones)
* duality theory for `FG` pointed cones, in particular, a version of the Minkowski-Weyl theorem that also works in infinite dimensional modules.
* polyhedral cones as cones that can be written as the sum of an `FG` cone and a submodule.
* duality theory of polyhedral cones
* faces and exposed faces of cones
* the face lattice of a cone
* Krein-Milman theorem for FG cones
* a proof that face lattices of finitely generated cones are graded
* convex sets, polytopes and polyhedra in `ConvexSpace`
* faces of convex sets

A detailed overview of the most relevant open and merged PRs is given in the Zulip thread ["PRs for polyhedral geometry and combinatorics"](https://leanprover.zulipchat.com/#narrow/channel/144837-PR-reviews/topic/PRs.20for.20polyhedral.20geometry.2Fcombinatorics/with/579565921).

<!--
- Lineality space of a cone: [#33780](https://github.com/leanprover-community/mathlib4/pull/33780) (merged)
- Face-lattices of cones: [#33664](https://github.com/leanprover-community/mathlib4/pull/33664)
- Duality operator for submodules: [#34007](https://github.com/leanprover-community/mathlib4/pull/34007)
- Cone duality theory: [#35323](https://github.com/leanprover-community/mathlib4/pull/35323) (merged)
- Duals of finitely generated cones: [#36946](https://github.com/leanprover-community/mathlib4/pull/36946) (merged)
-->

<!-- not a serious PR (!) - https://github.com/leanprover-community/mathlib4/pull/34703 -->

<!--
## Minor PRs
- https://github.com/leanprover-community/mathlib4/pull/33980
- https://github.com/leanprover-community/mathlib4/pull/33761
- https://github.com/leanprover-community/mathlib4/pull/33993
- https://github.com/leanprover-community/mathlib4/pull/33986
- https://github.com/leanprover-community/mathlib4/pull/33924
- coercion submodule => cone: https://github.com/leanprover-community/mathlib4/pull/35308
- pointwise negation lemma: https://github.com/leanprover-community/mathlib4/pull/36634/changes
- Interaction of cone span, linear span and negation [#36605](https://github.com/leanprover-community/mathlib4/pull/36605)
- Submodules over a ring are modular elements in the lattice of submodules over a semiring: [#36689](https://github.com/leanprover-community/mathlib4/pull/36689)
- Instances for SeparatingLeft, SeparatingRight and Nondegenerate: [#34487](https://github.com/leanprover-community/mathlib4/pull/34487)
- Co-finitely generated submodules: [#34006](https://github.com/leanprover-community/mathlib4/pull/34006)
- Renaming PointedCone.span to PointedCone.hull: #36953


-->
