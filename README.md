
# Polyhedral theory in mathlib

The goal of this project is to provide a flexible and useful implementation of polyhedral geometry/combinatorics in Lean, for `mathlib`, on which more advanced polyhedral theory can be built. Currently we focus on polyhedral cones, but there is a clear plan for how to move to polyhedra and polytopes. To get to a point where we can implement and work with polyhedral cones comfortably, we also needed to implement duality theory, co-finitely generated subspaces, faces of cones and many more details.

Currently the project implements:
* the `corank` of a submodule
* co-finitely generated submodules (`CoFG`)
* duality for submodules w.r.t. a general bilinear pairing.
* dual closed subspaces (`IsDualClosed`) which expresses that a subspace is its own double dual.
* `FGDual` submodules, which are the dual of `FG` (finitely generated) submodules.
* duality theory of `FG` submodules
* dual closed polyhedral cones
* `FGDual` pointed cones
* duality theory of `FG` pointed cones, in particular, a version of the Minkowski-Weyl theorem that works to infinite dimensional modules.
* polyhedral cones as cones that can be expressed as the sum of an `FG` cone and a submodule.
* duality theory of polyhedral cones.
* faces and exposed faces of cones
* the face lattice of a cone
* face theorey of polyhedral cones (all faces are exposed, the face lattice is graded, etc.)

<!--blueprint:  https://ooovi.github.io/Polyhedral/-->
