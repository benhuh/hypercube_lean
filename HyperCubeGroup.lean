/-
  HyperCubeGroup: Lean 4 Formalization of
  "Theoretical Framework for Discovering Groups and
   Unitary Representations via Tensor Factorization"

  Core results formalized:
  - Orthogonal decomposition H = B + R (Lemma 3)
  - Collinear manifold analysis: shared Gram matrices,
    normalized rank, AM-GM lower bound (Lemmas 10-12)
  - Group isotope characterization (Theorems 6-8)
-/

import HyperCubeGroup.Basic
import HyperCubeGroup.Decomposition
import HyperCubeGroup.CollinearManifold
import HyperCubeGroup.GroupIsotope
import HyperCubeGroup.Abelian
import HyperCubeGroup.Spectral
import HyperCubeGroup.BlockCyclic
import HyperCubeGroup.MatrixAMGM
import HyperCubeGroup.Plancherel
import HyperCubeGroup.PontryaginBridge
import HyperCubeGroup.ActiveSubspaceGeneric
import HyperCubeGroup.ActiveSubspace
import HyperCubeGroup.ActiveSubspaceConstruction
import HyperCubeGroup.Tikhonov
import HyperCubeGroup.Coercivity
