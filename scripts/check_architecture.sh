#!/usr/bin/env bash
set -euo pipefail

obsolete='Augmentation''AssociatedGradedData'
! grep -R -n -- "$obsolete" Amenability

! grep -n -E '^import Amenability\.(Theorem[A-J]|HopfAmenability|HopfAlgebraAmenability|CleftAmenability|ProjectiveAmenability)' \
  Amenability/AugmentationFiltration.lean \
  Amenability/AugmentationGradedAlgebra.lean \
  Amenability/AugmentationGradedModule.lean \
  Amenability/AugmentationGradedCoalgebra.lean \
  Amenability/AugmentationGradedHopf.lean \
  Amenability/AugmentationGradedHopfModuleCoalgebra.lean \
  Amenability/AugmentationLeadingSymbols.lean \
  Amenability/TensorFiltrationIntersection.lean \
  Amenability/TensorFiltrationGraded.lean \
  Amenability/TripleFiltrationGraded.lean \
  Amenability/FilteredInitial.lean

! grep -n -E '^import Amenability\.(Theorem[A-J]|LieGeneratorTest|Hopf.*Amenability)' \
  Amenability/SubexponentialGrowth.lean \
  Amenability/AlgebraGrowth.lean \
  Amenability/LieGrowth.lean \
  Amenability/UniversalEnvelopingGrowth.lean

for f in Amenability/Theorem{A,B,C,D,E,F,G,H,I,J}.lean; do
  grep -q -E '(^|[[:space:]])(theorem|def|structure|instance)[[:space:]]' "$f"
done
