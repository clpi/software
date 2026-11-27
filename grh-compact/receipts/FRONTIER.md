# Single-replacement frontier (no new axioms)

Each row: a local lemma whose own proof is the only route to the listed Mathlib constants in the RH closure (dominator tree of the original 219,974-constant closure). Re-proving that lemma without them removes exactly that many constants. Done: rows marked DONE.

| Mathlib constants carried | Local lemma | Module | Main entry points |
|---|---|---|---|
| 13124 | _private.Lib.GaloisRep.Main.SeedRepresentation.0.New.GaloisRep.exists_padicRep_of_pel | Lib.GaloisRep.Main.SeedRepresentation | AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology (799), AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite (797) |
| 8270 | New.Variety.Model.exists_galois_rep | Lib.Shimura.Eigenspace | CategoryTheory.IsGrothendieckAbelian.enoughInjectives (2120), CochainComplex.mappingCone.quasiIso_descShortComplex (315) |
| 1436 | New.Selmer.exists_mFoldTwist_hasDenominatorsLe | New.Congruences.FitTwistsExist | WittVector.mkUnit (47), Finite.isField_of_domain (26) |
| 1349 | New.tate_index_formula_norm DONE | Lib.ClassField.GaloisCohomology.TateIndexFormula | groupCohomology.exists_div_of_norm_eq_one (1344), Representation.mem_invariants_iff_of_forall_mem_zpowers (2) |
| 764 | New.exists_eigenvector_of_commute DONE | Lib.General.LinearAlgebra.Eigenvalues | LieModule.exists_forall_lie_eq_smul (312), LieModule.genWeightSpaceOf._proof_4 (153) |
| 572 | New.Variety.exists_thetaFamily_of_points | Lib.Shimura.ThetaModuli.FamilyFromPoints | Algebra.FormallySmooth.of_perfectField (526), AlgebraicGeometry.LocallyOfFiniteType.stalkMap (16) |
| 508 | New.exists_pow_mul_norm_fourier_le | Lib.General.Analysis.FourierTransforms | SchwartzMap.fourierTransformCLM (91), ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear (67) |
| 338 | New.GaloisRep.IsSplitPrimeToDisc.exists_place_above_ne | Lib.GaloisRep.Main.QuadraticStep | IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (64), IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd (44) |
| 264 | New.HCParam.dsCoeffSmooth._proof_1 | Lib.DiscreteSeries.FlenstedJensen.CasimirEigenfunction | SmoothPartitionOfUnity.exists_isSubordinate (230), contMDiff_finsum (8) |
| 263 | New.smooth_of_allSpecializeTo_isReduced | Lib.Shimura.ThetaModuli.FamilyFromPoints | AlgebraicGeometry.instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact (225), AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso (20) |
| 256 | New.GaloisRep.exists_weak_baseChange | Lib.GaloisRep.Main.OddRank | IsZGroup.instIsCyclicOfFiniteOfIsNilpotent (225), IsZGroup.instQuotientSubgroupOfFinite (15) |
| 240 | New.index_stabilizer_line | Lib.Weil.Unramified.HeckeGL | Projectivization.prePrimitive_SL (198), MulAction.IsPreprimitive.isQuasiPreprimitive (18) |
| 205 | New.Data.integral_forms_long | New.Determinant.Twist.LongForms | Projectivization.nonZeroEquivProjectivizationProdUnits (29), WithVal.instNumberField (12) |
| 188 | New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div | New.Determinant.Twist.LongForms | Nat.sum_four_squares (41), IsBaseChange.basis._proof_5 (17) |
| 183 | New.exists_isRegularFamily | New.Congruences.FitTwistsExist | nsmul_eq_zero_iff_of_coprime (17), cyclotomicCharacter.toZModPow_toFun (16) |
| 161 | New.Variety.exists_locallyOfFiniteType_forall_factors | Lib.General.Geometry.PointsOfProperSchemes | TopologicalSpace.Clopens.instBooleanAlgebra (61), PrimeSpectrum.isIdempotentElemEquivClopens (38) |
| 148 | New.Variety.Model.isNullHecke_mul_of_kills_weight | Lib.Shimura.Eigenspace | CliffordAlgebra.left_induction (74), CliffordAlgebra.contractLeft (9) |
| 145 | New.isProper_pi | Lib.General.Geometry.SerreTheorem | CategoryTheory.MorphismProperty.Over.instCreatesFiniteLimitsTopOverForget (67), CategoryTheory.MorphismProperty.Over.instHasFiniteLimitsTopOfHasFiniteWidePullbacks (39) |
| 130 | New.ProjSpace.isProper_specZIsTerminal_from | Lib.General.Geometry.ProjectiveSpace | AlgebraicGeometry.Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat (118), AlgebraicGeometry.Proj.basicOpen_one (3) |
| 130 | New.Variety.exists_perfection_quotient | Lib.General.Algebra.PerfectAlgebras | PerfectClosure.instCommRing (51), PerfectClosure.instCommMonoid (13) |
| 123 | New.exists_nnreal_valuation | Lib.General.Geometry.DenseComplexPoints | ValuativeRel.isRankLeOne_iff_mulArchimedean (109), ValuativeRel.valuation_surjective (2) |
| 119 | New.rightDerivMatrix._proof_6 | Lib.DiscreteSeries.FlenstedJensen.RightDerivatives | VectorField.fderiv_apply_lieBracket (111), wrapped._@.Mathlib.Analysis.Calculus.FDeriv.Symmetric.2709261267._hygCtx._hyg.40 (2) |
| 117 | New.Variety.exists_cell_over | Lib.PadicComparison.Descent.TestCovers | Filter.Germ.instCommRing (56), Filter.Germ.instMonoid (11) |
| 112 | New.Variety.cancels_moebius_of_factorsThrough_sup | Lib.Shimura.IntegralModel.TowerExistence | IncidenceAlgebra.moebius_inversion_bot (93), _private.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra.0.IncidenceAlgebra.muFun_apply (5) |
| 104 | New.DiscreteSeries.exists_conj_mem_dilationGroup | Lib.DiscreteSeries.CuspKernel | IsSelfAdjoint.norm_sub_eq_max (104) |
| 104 | New.Variety.mayer_vietoris_shortExact | Lib.Cohomology.Etale.DenseSubfunctors | CategoryTheory.Limits.Types.isPushout_of_bicartSq (77), CategoryTheory.IsPushout.of_forall_isPushout_app (6) |
| 104 | New.GaloisRep.exists_rep_of_cuspidal_type | Lib.GaloisRep.Main.SeedRepresentation | MvPolynomial.totalDegree_mul_of_isDomain (49), MvPolynomial.uniqueFactorizationMonoid (12) |
| 102 | New.Core.exists_form_eq_one | Lib.Adelic.Landherr | QuadraticAlgebra.instCommRing (21), QuadraticAlgebra.instCommSemiring (13) |
| 100 | New.card_freeEntry_level | New.Spanning.Unfolding.ReducedGroups | Fintype.card_product_filter_lt (98), Nat.add_choose_eq (2) |
| 99 | New.Variety.instIsGrothendieckAbelianAbFunctor | Lib.Cohomology.Etale.Basic | Ab.ab5OfSize (27), CategoryTheory.Presheaf.hasSeparator (25) |
| 95 | New.Variety.ContinuousUpTo.of_cech | Lib.Cohomology.Etale.FilteredLimits | CategoryTheory.Limits.instPreservesFiniteLimitsFunctorColimOfPreservesColimitsOfShapeOfHasFiniteLimitsOfReflectsIsomorphismsForget (94), CategoryTheory.MorphismProperty.colimMap (1) |
| 92 | New.IsTraceNondeg.of_span_piMatrix | Lib.GaloisRep.Pseudocharacter.SemisimpleRepresentations | IsSemisimpleRing.instMatrix (92) |
| 88 | New.Fock.norm_pairHom_le | Lib.Weil.Fock.OscillatorPair | Matrix.kroneckerStarAlgEquiv (52), MulOpposite.instNonUnitalCStarAlgebra (28) |
| 81 | New.DiscreteSeries.eq_zero_of_mem_fixed_invariant | Lib.DiscreteSeries.CuspKernel | BoundedContinuousFunction.instCommCStarAlgebra (37), BoundedContinuousFunction.instNonUnitalCStarAlgebra (14) |
| 79 | New.instProperSpaceLocField | Lib.Adelic.Adeles.Basic | Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField (79) |
| 78 | New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero | Lib.Analytic.ZeroSymmetry | DirichletCharacter.IsPrimitive.completedLFunction_one_sub (76), DirichletCharacter.rootNumber._proof_1 (1) |
| 77 | New.tendsto_pow_pow_of_norm_sub_one_lt | Lib.General.NumberTheory.PadicLimitsValuation | PadicInt.continuousAddCharEquiv_of_norm_mul (49), PadicInt.mahlerSeries_apply_nat (11) |
| 73 | New.hasDerivAt_betaFactor | Lib.CM.KroneckerLimit | Real.hasDerivAt_Gamma_one_half (47), Real.deriv_Gamma_nat (20) |
| 72 | New.Lift.Chart.weierstrass_division | Lib.PadicHodge.Kisin.Charts | PowerSeries.exists_isWeierstrassDivision (28), PowerSeries.IsWeierstrassDivision.elim (10) |
| 70 | New.Variety.exists_basis_forms_lerayHirsch | Lib.Cohomology.Hodge.Kunneth | Sum.Lex.linearOrder (23), OrderIso.sumCongr (18) |
