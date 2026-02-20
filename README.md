
# Polyhedral theory in mathlib

The goal of this project is to provide a flexible and useful implementation of polyhedral geometry/combinatorics in Lean, for `mathlib`, on which more advanced theory can be built. Currently we focus on polyhedral cones since convexity on affine spaces is not yet well developed in mathlib. There is a clear plan for how to move to polyhedra and polytopes eventually. To get to a point where we can implement and work with polyhedral cones comfortably, we also needed to implement duality theory, co-finitely generated subspaces, faces of cones and many more details.

Currently the project implements:
* co-finitely generated submodules (`CoFG`)
* duality for submodules w.r.t. a general bilinear pairing.
* dual closed subspaces (`DualClosed`) which expresses that a subspace is its own double dual.
* `FGDual` submodules, which are the dual of `FG` (finitely generated) submodules.
* duality theory for `FG` submodules
* dual closed pointed cones
* `FGDual` pointed cones
* duality theory for `FG` pointed cones, in particular, a version of the Minkowski-Weyl theorem that works to infinite dimensional modules.
* polyhedral cones as cones that can be written as the sum of an `FG` cone and a submodule.
* duality theory of polyhedral cones
* faces and exposed faces of cones
* the face lattice of a cone
* face theory of polyhedral cones (all faces are exposed, the face lattice is graded, etc.)

<!--blueprint:  https://ooovi.github.io/Polyhedral/-->
## On it's way
- Face-lattices of cones: [#33664](https://github.com/leanprover-community/mathlib4/pull/33664)
- Duality operator for submodules: [#34007](https://github.com/leanprover-community/mathlib4/pull/34007)
- instances for SeparatingLeft, SeparatingRight and Nondegenerate: [#34487](https://github.com/leanprover-community/mathlib4/pull/34487)
<!-- not a serious PR (!) - https://github.com/leanprover-community/mathlib4/pull/34703 -->

## Merged PRs
- Co-finitely generated submodules: [#34006](https://github.com/leanprover-community/mathlib4/pull/34006)

<!--
## Minor PRs
- https://github.com/leanprover-community/mathlib4/pull/33980
- https://github.com/leanprover-community/mathlib4/pull/33761
- https://github.com/leanprover-community/mathlib4/pull/33993
- https://github.com/leanprover-community/mathlib4/pull/33986
- https://github.com/leanprover-community/mathlib4/pull/33924
-->
