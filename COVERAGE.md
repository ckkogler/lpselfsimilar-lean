# Mathematical coverage

The primary sources are Samuel Kittle and Constantin Kogler, *On Lp density
of self similar measures and Bernoulli convolutions* and *A cubic criterion
for continuous algebraic Bernoulli convolutions*. Bibliographic attribution
is in [provenance/BIBLIOGRAPHY.md](provenance/BIBLIOGRAPHY.md).

The source map below distinguishes the compact introduction claims from the
full supporting library. Source correspondence and migration are being checked;
completed verification is recorded separately in [verification](verification/README.md).
Names have prefix `LpSelfSimilar` unless fully qualified.

## Introduction claims

| Source | Declaration | Content |
| --- | --- | --- |
| First paper, Theorem 1.1 | `self_similar_higher_integrability`, [SelfSimilar/HigherIntegrability](LpSelfSimilar/SelfSimilar/HigherIntegrability.lean) | Absolutely continuous stationary probability measures for finite contracting Euclidean similarity systems have a nonnegative Lp density for some p>1. Different ratios, overlaps, reflections and zero weights are allowed. |
| First paper, Theorem 1.2 | `algebraic_bernoulli_convolution_continuous_density_non_strict`, [Algebraic/ContinuousDensityEndpoint](LpSelfSimilar/Algebraic/ContinuousDensityEndpoint.lean) | The exact canonical degree/Mahler criterion with exponent 100 and a non-strict endpoint gives a continuous compactly supported density. |
| First paper, Theorem 1.3; cubic paper, Theorem 1.1 | `algebraic_bernoulli_convolution_cubic`, [Algebraic/CubicContinuity](LpSelfSimilar/Algebraic/CubicContinuity.lean) | The non-strict exponent-three criterion gives both L2 density at lambda squared and continuous compactly supported density at lambda. |
| First paper, Corollary 1.4; cubic paper, Corollary 1.2 | `rational_bernoulli_convolution_continuous_density_cubic`, [Rational/CubicContinuity](LpSelfSimilar/Rational/CubicContinuity.lean) | For reduced lambda=1-p/q, the exact sufficient condition is p<=q/(2+log q)^3. |
| Cubic paper, Corollary 1.2, integer consequence | `bernoulli_convolution_one_sub_inv_continuous_density_cubic_int`, [Rational/CubicIntegerFamily](LpSelfSimilar/Rational/CubicIntegerFamily.lean) | Every integer n>=588 gives continuity at 1-1/n; the exact sufficient-condition threshold is proved separately. |

These five claims appear in [Challenge.lean](Challenge.lean), with ordinary
independent definitions. The cubic theorem has both conclusions in one
conjunctive declaration. Duplicate statements in the two sources are compared
once. Supporting results are not additional public Challenge claims.

## First paper: supporting results

| Source | Declaration or modules | Preserved content |
| --- | --- | --- |
| Lemma 2.1 | `weak_reverse_holder_eighteen`, [WeakReverseHolder/SharpTheorem](LpSelfSimilar/WeakReverseHolder/SharpTheorem.lean) | C=18^d and p=1+log(1/(C eta))/log(C/epsilon), with the full stated range of epsilon and eta. This is a new strengthened theorem, not the older 21^d lemma. |
| Level recurrence (2.2) | `weak_reverse_holder_level_recurrence`, [WeakReverseHolder/SharpSourceRecurrence](LpSelfSimilar/WeakReverseHolder/SharpSourceRecurrence.lean); [WeakReverseHolder/SharpSourceConstants](LpSelfSimilar/WeakReverseHolder/SharpSourceConstants.lean) | The exact strict-superlevel recurrence with A=18^d/epsilon and gamma=2*6^d eta, above an explicit positive threshold. Its endpoint summation ratio is exactly 2*(1/3)^d<=2/3. |
| Stopped-scale mass estimate (2.3) | [SelfSimilar/SmallSetEstimate](LpSelfSimilar/SelfSimilar/SmallSetEstimate.lean), [SelfSimilar/HigherIntegrability](LpSelfSimilar/SelfSimilar/HigherIntegrability.lean) | Local small-set mass control from actual stationarity, support and contraction; finite stopping-word partitions give the averaged law. |
| Proposition 3.1 | `Algebraic.higher_integrability`, [Algebraic/HigherIntegrability](LpSelfSimilar/Algebraic/HigherIntegrability.lean) | The exact smallness hypothesis chi B^10<=10^(-100) gives an L^(1+delta) density, delta=1/(10(1-log(1-lambda))). |
| Lemma 3.2 | `Revised.scaled_finite_convolution_continuous_density`, `Revised.scaled_finite_convolution_continuous_density_ennreal`, [Revised/ScaledYoung](LpSelfSimilar/Revised/ScaledYoung.lean) | Arbitrary positive scales, compactly supported probability densities and p>=k/(k-1), including p=infinity, give a continuous compactly supported convolution density. |
| Power selection and (3.3) | `Revised.smoothingPower_spec`, `Revised.logarithmic_gap_bounds`, `Revised.smoothingPower_cost_bound`, [Revised/PowerSelection](LpSelfSimilar/Revised/PowerSelection.lean) | The exact floor choice k=floor(20-20 log(1-lambda)), the bounds 100 log B<=t<=B and 400<t, and its exponential cost estimate. Monotonicity and a rational certificate establish the numerical endpoint at t=400. |
| Lemma 3.3 | `Revised.density_memLp_of_bounded_approximation`, `Revised.density_memLp_of_L1_Linfty_approximation`, [Revised/BoundedApproximation](LpSelfSimilar/Revised/BoundedApproximation.lean) | The stated L1 error and bounded approximation imply the exact quantitative gain for the given density. |
| Gaussian normalization | [Gaussian/ExactNormalization](LpSelfSimilar/Gaussian/ExactNormalization.lean) | Q=sqrt(pi exp(1)/2), with 2<Q<21/10. |
| Detail identities (3.6)–(3.7) | [Gaussian/IntegratingScales](LpSelfSimilar/Gaussian/IntegratingScales.lean), [Gaussian/HigherDetail](LpSelfSimilar/Gaussian/HigherDetail.lean), [Gaussian/Semigroup](LpSelfSimilar/Gaussian/Semigroup.lean) | Smoothing-difference integral, convolution product bound, universal bound and exact Gaussian detail. |
| Lemma 3.4 | `Revised.detail_le_of_higherDetail_radius`, `Revised.detail_le_sup_higherDetail`, [Revised/DetailComparison](LpSelfSimilar/Revised/DetailComparison.lean) | Exact higher-to-first detail estimate with factor10^k, interval r/sqrt(k)<=t<=b, error r^2/b^2, including k=1. |
| Lemma 3.5 | `Gaussian.integrating_detail_explicit`, [Gaussian/SharpIntegratingDetail](LpSelfSimilar/Gaussian/SharpIntegratingDetail.lean) | Density and exact L1 approximation bound 4 delta R0+1/(4 R0). |
| Proposition 3.6 | `Algebraic.effective_detail`, [Algebraic/EffectiveDetail](LpSelfSimilar/Algebraic/EffectiveDetail.lean); `Bernoulli.weak_smoothing_explicit`, [Bernoulli/SharpWeakSmoothing](LpSelfSimilar/Bernoulli/SharpWeakSmoothing.lean) | Higher-detail bound with R0=10^6 B^3 and the all-scale 40 chi^(1/3) estimate. |
| Lemma 3.7 | `Gaussian.small_summands_independent`, [Gaussian/SharpSmallSummands](LpSelfSimilar/Gaussian/SharpSmallSummands.lean) | Independent bounded summands, exact variance denominator and error30 epsilon. |
| Lemma 3.8 | `Gaussian.conditional_variance_detail_explicit`, [Gaussian/GeneralConditionalVariance](LpSelfSimilar/Gaussian/GeneralConditionalVariance.lean) | Actual arbitrary conditioning sigma-algebras, measurable centers, epsilon0=10^(-4), variance budget1001 k r^2 and detail100^(-k). |
| Lemma 3.9 | `Entropy.gridEntropy_increment_le_ten_condVar_fourthRoot`, [Entropy/RandomGridVariance](LpSelfSimilar/Entropy/RandomGridVariance.lean) | Uniformly shifted grid entropy and actual expected conditional variance; exact constant10 and exponent1/4. |
| Lemma 3.10 | `Algebraic.arithmetic_input`, [Algebraic/ArithmeticInput](LpSelfSimilar/Algebraic/ArithmeticInput.lean) | All four complexity, separation, entropy and logarithmic gap estimates for the canonical algebraic invariants. |
| Lemma 3.11 | `Algebraic.digit_scaleVariance_integral_lower_bound`, [Algebraic/BlockVariance](LpSelfSimilar/Algebraic/BlockVariance.lean) | The exact scale-integrated digit-block variance bound. |

The older reverse Hölder result, strict exponent-100 statement, explicit rational
exponent-100 criterion and uniform exponent-50 criterion are preserved as library
results, with their own original hypotheses. They do not replace revised claims.

## Cubic proof and appendices

The following table follows the mathematical dependency order and includes the
working regularity criterion, arithmetic and entropy inputs, independent packing,
Fourier estimates, Gaussian approximation, concentration and both appendices.
Canonical definitions and density representations are shared with the first
proof route. The listed supporting anchors are indexed for inspection, while
Verification audits every imported authored declaration.

| Mathematical content | Modules |
| --- | --- |
| Series law, fair signs, independence, convergence and support | [Bernoulli/Construction](LpSelfSimilar/Bernoulli/Construction.lean); [Bernoulli/Digits](LpSelfSimilar/Bernoulli/Digits.lean); [Bernoulli/Residues](LpSelfSimilar/Bernoulli/Residues.lean); [Bernoulli/ResidueLaw](LpSelfSimilar/Bernoulli/ResidueLaw.lean) |
| Cubic non-strict endpoint and both density conclusions | [Algebraic/CubicContinuity](LpSelfSimilar/Algebraic/CubicContinuity.lean) |
| Reduced rational criterion and canonical rational identification | [Rational/CubicParameters](LpSelfSimilar/Rational/CubicParameters.lean); [Rational/CubicContinuity](LpSelfSimilar/Rational/CubicContinuity.lean) |
| Integer family, exact sufficient-condition threshold and endpoint certificates | [Rational/CubicIntegerFamily](LpSelfSimilar/Rational/CubicIntegerFamily.lean); [Analysis/CubicRationalThreshold](LpSelfSimilar/Analysis/CubicRationalThreshold.lean); [Analysis/CubicThresholdNumerics](LpSelfSimilar/Analysis/CubicThresholdNumerics.lean) |
| Even/odd independent convolution and L2-to-continuity argument | [Bernoulli/ConvolutionPowers](LpSelfSimilar/Bernoulli/ConvolutionPowers.lean); [Bernoulli/ContinuousDensity](LpSelfSimilar/Bernoulli/ContinuousDensity.lean) |
| Full entropy/separation working criterion and strict Gaussian L1 error | [Bernoulli/WorkingRegularityCriterion](LpSelfSimilar/Bernoulli/WorkingRegularityCriterion.lean) |
| Nonzero integral resultant, conjugate evaluation and strict distinct-atom separation | [Algebraic/PolynomialSeparation](LpSelfSimilar/Algebraic/PolynomialSeparation.lean); [Algebraic/DegreeMahlerScale](LpSelfSimilar/Algebraic/DegreeMahlerScale.lean) |
| Evaluation at one and exact degree/Mahler logarithmic gap | [Algebraic/GapEstimate](LpSelfSimilar/Algebraic/GapEstimate.lean); [Algebraic/DegreeMahlerScale](LpSelfSimilar/Algebraic/DegreeMahlerScale.lean) |
| Finite natural-log entropy, exact 3/10 and 1/2 coefficients and nonunits | [Algebraic/StrongDigitEntropy](LpSelfSimilar/Algebraic/StrongDigitEntropy.lean) |
| Positive logarithmic Mahler measure and complexity range | [Algebraic/Complexity](LpSelfSimilar/Algebraic/Complexity.lean); [Algebraic/CubicScaleBounds](LpSelfSimilar/Algebraic/CubicScaleBounds.lean) |
| Exact degree and logarithmic Mahler identities under squaring | [Algebraic/DegreeMahlerPowers](LpSelfSimilar/Algebraic/DegreeMahlerPowers.lean); [Algebraic/MinimalPolynomialSquaring](LpSelfSimilar/Algebraic/MinimalPolynomialSquaring.lean); [Algebraic/SquaredConjugates](LpSelfSimilar/Algebraic/SquaredConjugates.lean) |
| Logarithmic cubic constraint, concavity, B>8 and B>11 exclusions | [Analysis/CubicLogExclusions](LpSelfSimilar/Analysis/CubicLogExclusions.lean); [Analysis/CubicScaleConstraints](LpSelfSimilar/Analysis/CubicScaleConstraints.lean); [Algebraic/CubicScaleBounds](LpSelfSimilar/Algebraic/CubicScaleBounds.lean) |
| Squared-parameter range, exact logarithmic gap and 1/250 bound | [Analysis/CubicLogGap](LpSelfSimilar/Analysis/CubicLogGap.lean); [Algebraic/CubicSquareSmallness](LpSelfSimilar/Algebraic/CubicSquareSmallness.lean) |
| Bits conversion, positivity, L>=3, cell bound and entropy for the square | [Algebraic/CubicCriterionParameters](LpSelfSimilar/Algebraic/CubicCriterionParameters.lean); [Algebraic/CubicSquareEntropy](LpSelfSimilar/Algebraic/CubicSquareEntropy.lean) |
| Both smallness branches, monotone log ratios and displayed numerical margins | [Analysis/CubicEndpointNumerics](LpSelfSimilar/Analysis/CubicEndpointNumerics.lean); [Analysis/CubicLogRatios](LpSelfSimilar/Analysis/CubicLogRatios.lean); [Analysis/CubicSmallness](LpSelfSimilar/Analysis/CubicSmallness.lean); [Algebraic/CubicSquareSmallness](LpSelfSimilar/Algebraic/CubicSquareSmallness.lean) |
| Exact packing parameters and their elementary ranges | [Bernoulli/PackingParameters](LpSelfSimilar/Bernoulli/PackingParameters.lean) |
| Actual merged-law measurable distance-band entropy budget | [Entropy/MeasurableBandConditionals](LpSelfSimilar/Entropy/MeasurableBandConditionals.lean); [Entropy/FiniteLawBandEntropy](LpSelfSimilar/Entropy/FiniteLawBandEntropy.lean); [Bernoulli/DigitBandEntropy](LpSelfSimilar/Bernoulli/DigitBandEntropy.lean) |
| Full sixteen-atom cancellation inequality for every positive alpha | [Entropy/SixteenAtomCancellation](LpSelfSimilar/Entropy/SixteenAtomCancellation.lean); [Entropy/FiniteCancellation](LpSelfSimilar/Entropy/FiniteCancellation.lean) |
| Exact scalar second derivative, concavity, both delta ranges and chord | [Analysis/CancellationProfile](LpSelfSimilar/Analysis/CancellationProfile.lean); [Analysis/LargeMassCancellation](LpSelfSimilar/Analysis/LargeMassCancellation.lean) |
| Dominant-atom entropy grouping, zero masses and attained variational identity | [Entropy/DominantAtomGrouping](LpSelfSimilar/Entropy/DominantAtomGrouping.lean); [Entropy/BinaryVariational](LpSelfSimilar/Entropy/BinaryVariational.lean) |
| Exact alpha/beta specialization and logarithmic remainder bound | [Entropy/CancellationParameters](LpSelfSimilar/Entropy/CancellationParameters.lean); [Entropy/SixteenAtomCancellation](LpSelfSimilar/Entropy/SixteenAtomCancellation.lean) |
| Finite-n cancellation integral, exact W bound and cancellation range | [Entropy/ExplicitCancellationBudget](LpSelfSimilar/Entropy/ExplicitCancellationBudget.lean); [Entropy/CancellationRate](LpSelfSimilar/Entropy/CancellationRate.lean); [Entropy/JointCancellationBounds](LpSelfSimilar/Entropy/JointCancellationBounds.lean) |
| Finite geometric phase average, quadrature, tail weight and strict 0.6585 margin | [Analysis/GeometricQuadratureTail](LpSelfSimilar/Analysis/GeometricQuadratureTail.lean); [Analysis/GeometricPhaseAverage](LpSelfSimilar/Analysis/GeometricPhaseAverage.lean); [Analysis/GeometricPhaseConstants](LpSelfSimilar/Analysis/GeometricPhaseConstants.lean); [Analysis/GeometricPhaseLength](LpSelfSimilar/Analysis/GeometricPhaseLength.lean) |
| Squared transform identity, a common shift before sampling and support 52r | [Fourier/FinitePhaseCancellation](LpSelfSimilar/Fourier/FinitePhaseCancellation.lean); [Fourier/ScaledBandShift](LpSelfSimilar/Fourier/ScaledBandShift.lean); [Bernoulli/DigitBandBlock](LpSelfSimilar/Bernoulli/DigitBandBlock.lean) |
| Exact block-length parameters, attenuation and 1/15 cost bound | [Bernoulli/PackingParameters](LpSelfSimilar/Bernoulli/PackingParameters.lean); [Analysis/PackingNumericalBounds](LpSelfSimilar/Analysis/PackingNumericalBounds.lean); [Bernoulli/PackingAttenuation](LpSelfSimilar/Bernoulli/PackingAttenuation.lean) |
| Exact finite number of block lengths and largest-length cutoff | [Bernoulli/PackingLengths](LpSelfSimilar/Bernoulli/PackingLengths.lean); [Analysis/GeometricLengthCutoff](LpSelfSimilar/Analysis/GeometricLengthCutoff.lean) |
| Translated-grid averaging, endpoint losses, padding and retained attenuation | [Bernoulli/PackingGridSelection](LpSelfSimilar/Bernoulli/PackingGridSelection.lean); [Bernoulli/PackingGridBudget](LpSelfSimilar/Bernoulli/PackingGridBudget.lean); [Bernoulli/PackingPadding](LpSelfSimilar/Bernoulli/PackingPadding.lean); [Bernoulli/PackingEndpointError](LpSelfSimilar/Bernoulli/PackingEndpointError.lean) |
| Natural disjoint blocks, windows, counts, original labels and independent remainder | [Bernoulli/PackingGridCount](LpSelfSimilar/Bernoulli/PackingGridCount.lean); [Bernoulli/PackingLengthSeparation](LpSelfSimilar/Bernoulli/PackingLengthSeparation.lean); [Bernoulli/PackingNaturalBlocks](LpSelfSimilar/Bernoulli/PackingNaturalBlocks.lean); [Bernoulli/PackingConditionalDecomposition](LpSelfSimilar/Bernoulli/PackingConditionalDecomposition.lean) |
| Reserved unused tail, small angles, cosine Gaussian bound and exponential factor | [Bernoulli/ReservedTailIndex](LpSelfSimilar/Bernoulli/ReservedTailIndex.lean); [Bernoulli/ReservedTailAngles](LpSelfSimilar/Bernoulli/ReservedTailAngles.lean); [Bernoulli/ReservedTailFourier](LpSelfSimilar/Bernoulli/ReservedTailFourier.lean) |
| Summable tail coefficients, justified derivatives and exact order-zero/two bounds | [Bernoulli/ReservedTailCoefficients](LpSelfSimilar/Bernoulli/ReservedTailCoefficients.lean); [Bernoulli/ReservedTailDerivatives](LpSelfSimilar/Bernoulli/ReservedTailDerivatives.lean); [Bernoulli/ReservedTailProductDerivatives](LpSelfSimilar/Bernoulli/ReservedTailProductDerivatives.lean) |
| Exact quintic, support, endpoint regularity, three norms and half-factor inversion | [Fourier/QuinticCutoff](LpSelfSimilar/Fourier/QuinticCutoff.lean); [Fourier/QuinticCutoffSupport](LpSelfSimilar/Fourier/QuinticCutoffSupport.lean); [Fourier/QuinticDetailCurvatureIntegrals](LpSelfSimilar/Fourier/QuinticDetailCurvatureIntegrals.lean); [Fourier/QuinticBandInversion](LpSelfSimilar/Fourier/QuinticBandInversion.lean) |
| Conditional products and derivatives, normalization, translation and probability remainder | [Bernoulli/PackingDerivativeBounds](LpSelfSimilar/Bernoulli/PackingDerivativeBounds.lean); [Fourier/QuinticMeanInversion](LpSelfSimilar/Fourier/QuinticMeanInversion.lean); [Bernoulli/ConditionalTailInversion](LpSelfSimilar/Bernoulli/ConditionalTailInversion.lean) |
| Full smoothing estimate with exact prefactor in packed and tail-only ranges | [Bernoulli/DetailSmoothingEstimate](LpSelfSimilar/Bernoulli/DetailSmoothingEstimate.lean); [Bernoulli/PackingSmoothingEstimate](LpSelfSimilar/Bernoulli/PackingSmoothingEstimate.lean); [Bernoulli/ReservedTailSmoothing](LpSelfSimilar/Bernoulli/ReservedTailSmoothing.lean) |
| Summable scale intervals, exact geometric sum, R0 and prefactor bounds | [Bernoulli/IntegratedLogarithmicDetail](LpSelfSimilar/Bernoulli/IntegratedLogarithmicDetail.lean); [Bernoulli/PackingThresholdUpperBound](LpSelfSimilar/Bernoulli/PackingThresholdUpperBound.lean) |
| Exact envelope, derivative/monotonicity and endpoint certificate | [Bernoulli/IntegratedDetailEnvelope](LpSelfSimilar/Bernoulli/IntegratedDetailEnvelope.lean); [Bernoulli/IntegratedEnvelopeDerivative](LpSelfSimilar/Bernoulli/IntegratedEnvelopeDerivative.lean); [Bernoulli/IntegratedEnvelopeComparison](LpSelfSimilar/Bernoulli/IntegratedEnvelopeComparison.lean); [Bernoulli/IntegratedEnvelopeSmallness](LpSelfSimilar/Bernoulli/IntegratedEnvelopeSmallness.lean) |
| Kernel mass, justified scale differentiation/Fubini, L1 limit and actual-law density | [Fourier/QuinticKernelTransforms](LpSelfSimilar/Fourier/QuinticKernelTransforms.lean); [Fourier/QuinticKernelScaleDerivative](LpSelfSimilar/Fourier/QuinticKernelScaleDerivative.lean); [Fourier/QuinticSmoothingDensity](LpSelfSimilar/Fourier/QuinticSmoothingDensity.lean); [Bernoulli/SmoothingDensity](LpSelfSimilar/Bernoulli/SmoothingDensity.lean) |
| Strict smoothed Gaussian approximation and actual density error | [Bernoulli/SmoothedGaussianApproximation](LpSelfSimilar/Bernoulli/SmoothedGaussianApproximation.lean); [Bernoulli/GaussianApproximation](LpSelfSimilar/Bernoulli/GaussianApproximation.lean) |
| Normalized maps, first concentration, inverse volume, disjoint stopped events and coverage | [SelfSimilar/Concentration/ExactModulus](LpSelfSimilar/SelfSimilar/Concentration/ExactModulus.lean); [SelfSimilar/Concentration/SharpL2](LpSelfSimilar/SelfSimilar/Concentration/SharpL2.lean) |
| Exact mass recurrence endpoint, alpha, density tails, layer cake and constant 12 | [Analysis/MassDecayExponent](LpSelfSimilar/Analysis/MassDecayExponent.lean); [Analysis/SmallSetMassPowers](LpSelfSimilar/Analysis/SmallSetMassPowers.lean); [Analysis/DensityPowerTails](LpSelfSimilar/Analysis/DensityPowerTails.lean); [Analysis/SquareLayerCake](LpSelfSimilar/Analysis/SquareLayerCake.lean); [SelfSimilar/Concentration/PowerBounds](LpSelfSimilar/SelfSimilar/Concentration/PowerBounds.lean); [SelfSimilar/Concentration/PowerL2](LpSelfSimilar/SelfSimilar/Concentration/PowerL2.lean) |
| Actual variance, support normalization, half-L1 mass bound, Gaussian height and 0.911 margin | [Bernoulli/VarianceNormalization](LpSelfSimilar/Bernoulli/VarianceNormalization.lean); [Bernoulli/UnitIntervalNormalization](LpSelfSimilar/Bernoulli/UnitIntervalNormalization.lean); [Bernoulli/NormalizedGaussianHeight](LpSelfSimilar/Bernoulli/NormalizedGaussianHeight.lean); [Bernoulli/GaussianApproximationMassBound](LpSelfSimilar/Bernoulli/GaussianApproximationMassBound.lean); [Analysis/GaussianConcentrationConstants](LpSelfSimilar/Analysis/GaussianConcentrationConstants.lean); [Bernoulli/GaussianApproximationL2](LpSelfSimilar/Bernoulli/GaussianApproximationL2.lean) |
| Digit subadditivity, actual limiting entropy rate and finite-length domination | [Bernoulli/DigitEntropySubadditivity](LpSelfSimilar/Bernoulli/DigitEntropySubadditivity.lean); [Bernoulli/EntropyRate](LpSelfSimilar/Bernoulli/EntropyRate.lean); [Algebraic/EntropyRate](LpSelfSimilar/Algebraic/EntropyRate.lean) |
| Nonunit noncollision, contracting conjugate product and actual Gaussian matrix comparison | [Algebraic/ContractingConjugates](LpSelfSimilar/Algebraic/ContractingConjugates.lean); [Algebraic/ContractingMatrixNormalization](LpSelfSimilar/Algebraic/ContractingMatrixNormalization.lean); [Algebraic/StrongDigitEntropy](LpSelfSimilar/Algebraic/StrongDigitEntropy.lean) |
| Canonical RN differential entropy, actual integrability and supremum comparison | [Entropy/DifferentialEntropy](LpSelfSimilar/Entropy/DifferentialEntropy.lean); [Gaussian/BinaryDifferentialEntropy](LpSelfSimilar/Gaussian/BinaryDifferentialEntropy.lean); [Algebraic/GaussianEntropyRate](LpSelfSimilar/Algebraic/GaussianEntropyRate.lean) |
| Actual fair-sign/noise independence, conditional expectation/variance and information derivative | [Gaussian/BinaryProbabilitySpace](LpSelfSimilar/Gaussian/BinaryProbabilitySpace.lean); [Gaussian/BinaryConditionalExpectation](LpSelfSimilar/Gaussian/BinaryConditionalExpectation.lean); [Gaussian/BinaryConditionalVariance](LpSelfSimilar/Gaussian/BinaryConditionalVariance.lean) |
| Exact Gaussian profile, monotonicity, curvature, concavity and 0.313 margin | [Analysis/GaussianEntropyProfile](LpSelfSimilar/Analysis/GaussianEntropyProfile.lean); [Analysis/GaussianEntropyProfileConstants](LpSelfSimilar/Analysis/GaussianEntropyProfileConstants.lean); [Gaussian/BinaryInformationScaling](LpSelfSimilar/Gaussian/BinaryInformationScaling.lean) |
| Sign-estimator error, binary entropy, small-amplitude bound and strict 0.516 margin | [Gaussian/BinaryInformationDecoder](LpSelfSimilar/Gaussian/BinaryInformationDecoder.lean); [Gaussian/BinaryInformationBounds](LpSelfSimilar/Gaussian/BinaryInformationBounds.lean); [Entropy/BinaryDecoderBounds](LpSelfSimilar/Entropy/BinaryDecoderBounds.lean) |
| Attained graph entropy, independent cover sampling, KL/entropy identity and graph union | [Entropy/GraphEntropy](LpSelfSimilar/Entropy/GraphEntropy.lean); [Entropy/FiniteCoverInformation](LpSelfSimilar/Entropy/FiniteCoverInformation.lean); [Entropy/GraphConditionalDecomposition](LpSelfSimilar/Entropy/GraphConditionalDecomposition.lean); [Entropy/GraphUnion](LpSelfSimilar/Entropy/GraphUnion.lean) |
| Ordered chain/antichain construction and exact complementary entropy duality | [Entropy/PosetGraphDuality](LpSelfSimilar/Entropy/PosetGraphDuality.lean); [Entropy/DistanceGraphDuality](LpSelfSimilar/Entropy/DistanceGraphDuality.lean); [Entropy/GraphComplement](LpSelfSimilar/Entropy/GraphComplement.lean) |
| Actual distance-band conditional mixture, sixteen-point cardinality and exact endpoints | [Entropy/DistanceBandGraph](LpSelfSimilar/Entropy/DistanceBandGraph.lean); [Entropy/DistanceBandDecomposition](LpSelfSimilar/Entropy/DistanceBandDecomposition.lean); [Entropy/GraphConditionalVariational](LpSelfSimilar/Entropy/GraphConditionalVariational.lean) |
| Quantization, cell count, separated endpoint, monotonicity and four-scale telescoping | [Entropy/QuantizedNearEntropy](LpSelfSimilar/Entropy/QuantizedNearEntropy.lean); [Geometry/FiniteIntervalQuantization](LpSelfSimilar/Geometry/FiniteIntervalQuantization.lean); [Entropy/GraphSeparationScale](LpSelfSimilar/Entropy/GraphSeparationScale.lean); [Entropy/DistanceBandScaleBudget](LpSelfSimilar/Entropy/DistanceBandScaleBudget.lean); [Entropy/DistanceBandEntropyBudget](LpSelfSimilar/Entropy/DistanceBandEntropyBudget.lean) |
| Exact coefficient masses, tanh bound and variance-one law | [Bernoulli/VarianceNormalizedCoefficients](LpSelfSimilar/Bernoulli/VarianceNormalizedCoefficients.lean); [Bernoulli/VarianceNormalizedSums](LpSelfSimilar/Bernoulli/VarianceNormalizedSums.lean); [Bernoulli/VarianceNormalization](LpSelfSimilar/Bernoulli/VarianceNormalization.lean) |
| Weighted Plancherel with exact factor 1/2 and actual smoothed-law application | [Fourier/WeightedPlancherel](LpSelfSimilar/Fourier/WeightedPlancherel.lean); [Bernoulli/SmoothedGaussianPlancherel](LpSelfSimilar/Bernoulli/SmoothedGaussianPlancherel.lean) |
| Unit-angle tangent/log-cos remainders, convergent series and transform/derivative errors | [Analysis/LogCosineRemainder](LpSelfSimilar/Analysis/LogCosineRemainder.lean); [Analysis/FiniteLogCosineBounds](LpSelfSimilar/Analysis/FiniteLogCosineBounds.lean); [Bernoulli/LogarithmicRemainder](LpSelfSimilar/Bernoulli/LogarithmicRemainder.lean); [Bernoulli/LogarithmicRemainderDerivative](LpSelfSimilar/Bernoulli/LogarithmicRemainderDerivative.lean); [Bernoulli/LowFrequencyGaussianApproximation](LpSelfSimilar/Bernoulli/LowFrequencyGaussianApproximation.lean); [Bernoulli/LowFrequencyGaussianDerivative](LpSelfSimilar/Bernoulli/LowFrequencyGaussianDerivative.lean) |
| Exact Gaussian moments, integrated low-frequency energy and numerical C bound | [Gaussian/EvenMoments](LpSelfSimilar/Gaussian/EvenMoments.lean); [Gaussian/LowFrequencyConstant](LpSelfSimilar/Gaussian/LowFrequencyConstant.lean); [Bernoulli/LowFrequencyEnergy](LpSelfSimilar/Bernoulli/LowFrequencyEnergy.lean) |
| Small-digit tail, omission cost, characteristic derivative and cutoff energy | [Bernoulli/HighFrequencyParameters](LpSelfSimilar/Bernoulli/HighFrequencyParameters.lean); [Bernoulli/HighFrequencyTailBounds](LpSelfSimilar/Bernoulli/HighFrequencyTailBounds.lean); [Fourier/QuinticCutoffSlopeEnergy](LpSelfSimilar/Fourier/QuinticCutoffSlopeEnergy.lean); [Fourier/QuinticScaledSlopeEnergy](LpSelfSimilar/Fourier/QuinticScaledSlopeEnergy.lean); [Bernoulli/HighFrequencyEnergy](LpSelfSimilar/Bernoulli/HighFrequencyEnergy.lean) |
| Exact cutoff-width input, integrated high-frequency bound and exponential margins | [Bernoulli/PackingGaussianWidth](LpSelfSimilar/Bernoulli/PackingGaussianWidth.lean); [Bernoulli/HighFrequencyEnergyMargin](LpSelfSimilar/Bernoulli/HighFrequencyEnergyMargin.lean) |
| Gaussian tail moments, exact high-frequency bound and final norm splitting | [Gaussian/TailMoments](LpSelfSimilar/Gaussian/TailMoments.lean); [Gaussian/ScaledTailEnergy](LpSelfSimilar/Gaussian/ScaledTailEnergy.lean); [Bernoulli/GaussianHighFrequencyMargin](LpSelfSimilar/Bernoulli/GaussianHighFrequencyMargin.lean); [Bernoulli/SmoothedGaussianApproximation](LpSelfSimilar/Bernoulli/SmoothedGaussianApproximation.lean) |

## Cubic declaration anchors

Names are fully qualified. The environment-based audit covers every imported
authored declaration, including these supporting anchors.
Repeated use of a declaration in the table does not create a new theorem.

### [Algebraic/Complexity](LpSelfSimilar/Algebraic/Complexity.lean)

- `LpSelfSimilar.Algebraic.complexity_pos`
- `LpSelfSimilar.Algebraic.three_le_complexity`
- `LpSelfSimilar.Algebraic.degree_add_log_mahlerMeasure_le_complexity`
- `LpSelfSimilar.Algebraic.inv_complexity`

### [Algebraic/ContractingConjugates](LpSelfSimilar/Algebraic/ContractingConjugates.lean)

- `LpSelfSimilar.Algebraic.mem_contractingConjugates`
- `LpSelfSimilar.Algebraic.self_mem_contractingConjugates`
- `LpSelfSimilar.Algebraic.contractingConjugate_ne_zero`
- `LpSelfSimilar.Algebraic.prod_conjugate_norms_eq_one`
- `LpSelfSimilar.Algebraic.prod_contractingConjugate_norms_eq_inv_mahlerMeasure`

### [Algebraic/ContractingMatrixNormalization](LpSelfSimilar/Algebraic/ContractingMatrixNormalization.lean)

- `LpSelfSimilar.Algebraic.realContractingRoot_re_injective`
- `LpSelfSimilar.Algebraic.contractingConjugateMatrix_observations_separate`
- `LpSelfSimilar.Algebraic.exists_normalized_contracting_conjugate_unit`
- `LpSelfSimilar.Algebraic.exists_normalized_contracting_unit_with_direction`

### [Algebraic/CubicContinuity](LpSelfSimilar/Algebraic/CubicContinuity.lean)

- `LpSelfSimilar.algebraic_bernoulli_convolution_square_density_cubic`
- `LpSelfSimilar.algebraic_bernoulli_convolution_continuous_density_cubic`
- `LpSelfSimilar.algebraic_bernoulli_convolution_cubic`

### [Algebraic/CubicCriterionParameters](LpSelfSimilar/Algebraic/CubicCriterionParameters.lean)

- `LpSelfSimilar.Algebraic.cubicEntropyBits_pos`
- `LpSelfSimilar.Algebraic.cubicEntropyBits_le_one`
- `LpSelfSimilar.Algebraic.three_le_cubicSeparationBits`
- `LpSelfSimilar.Algebraic.cubicSeparationBits_div_cubicEntropyBits`
- `LpSelfSimilar.Algebraic.digit_entropy_ge_cubicEntropyBits`
- `LpSelfSimilar.Algebraic.cubicSeparationBits_rpow`
- `LpSelfSimilar.Algebraic.digitPMF_separation_cubicSeparationBits`
- `LpSelfSimilar.Algebraic.cubic_cell_log_bound`

### [Algebraic/CubicScaleBounds](LpSelfSimilar/Algebraic/CubicScaleBounds.lean)

- `LpSelfSimilar.Algebraic.cubic_hypothesis_scale_bounds`

### [Algebraic/CubicSquareEntropy](LpSelfSimilar/Algebraic/CubicSquareEntropy.lean)

- `LpSelfSimilar.Algebraic.algebraicEntropyLowerBound_square_ge`
- `LpSelfSimilar.Algebraic.cubicEntropyBits_square_ge`

### [Algebraic/CubicSquareSmallness](LpSelfSimilar/Algebraic/CubicSquareSmallness.lean)

- `LpSelfSimilar.Algebraic.cubic_square_range_and_gap`
- `LpSelfSimilar.Algebraic.cubic_square_packing_smallness`

### [Algebraic/DegreeMahlerPowers](LpSelfSimilar/Algebraic/DegreeMahlerPowers.lean)

- `LpSelfSimilar.Algebraic.degreeMahlerScale_pow_le_mul`
- `LpSelfSimilar.Algebraic.log_mahlerMeasure_square_eq`
- `LpSelfSimilar.Algebraic.square_degree_mahler_estimates`

### [Algebraic/DegreeMahlerScale](LpSelfSimilar/Algebraic/DegreeMahlerScale.lean)

- `LpSelfSimilar.Algebraic.degreeMahlerScale_pos`
- `LpSelfSimilar.Algebraic.log_inverse_gap_le_degree_mahler`
- `LpSelfSimilar.Algebraic.digitSum_separation_degree_mahler_scale`

### [Algebraic/EntropyRate](LpSelfSimilar/Algebraic/EntropyRate.lean)

- `LpSelfSimilar.Algebraic.entropyRate_eq_log_two_of_not_isAlgebraicUnit`
- `LpSelfSimilar.Algebraic.unit_entropyRate_ge_binary_information`
- `LpSelfSimilar.Algebraic.unit_information_gains_bddAbove`
- `LpSelfSimilar.Algebraic.unit_entropyRate_ge_sup_information`
- `LpSelfSimilar.Algebraic.unit_entropyRate_ge_gaussianEntropyProfile`
- `LpSelfSimilar.Algebraic.entropyRate_three_tenths_lower`
- `LpSelfSimilar.Algebraic.entropyRate_half_lower`
- `LpSelfSimilar.Algebraic.entropyRate_ge_algebraicEntropyLowerBound`
- `LpSelfSimilar.Algebraic.entropyRate_pos`

### [Algebraic/GapEstimate](LpSelfSimilar/Algebraic/GapEstimate.lean)

- `LpSelfSimilar.Algebraic.one_le_gap_mul_degree_mahler`
- `LpSelfSimilar.Algebraic.log_inverse_gap_le_complexity`

### [Algebraic/GaussianEntropyRate](LpSelfSimilar/Algebraic/GaussianEntropyRate.lean)

- `LpSelfSimilar.Algebraic.unit_entropyRate_ge_differentialEntropy_gain`
- `LpSelfSimilar.Algebraic.unit_differentialEntropy_gains_bddAbove`
- `LpSelfSimilar.Algebraic.unit_entropyRate_ge_sup_differentialEntropy`

### [Algebraic/MinimalPolynomialSquaring](LpSelfSimilar/Algebraic/MinimalPolynomialSquaring.lean)

- `LpSelfSimilar.Algebraic.integerMinimalPolynomial_dvd_square_expansion`
- `LpSelfSimilar.Algebraic.square_minimal_expansion_dvd_even_polynomial`
- `LpSelfSimilar.Algebraic.normalize_integerMinimalPolynomial_square_expansion`
- `LpSelfSimilar.Algebraic.integerMinimalPolynomial_square_of_even`
- `LpSelfSimilar.Algebraic.integerMinimalPolynomial_isRelPrime_reflection`
- `LpSelfSimilar.Algebraic.integerMinimalPolynomial_square_of_not_even`

### [Algebraic/PolynomialSeparation](LpSelfSimilar/Algebraic/PolynomialSeparation.lean)

- `LpSelfSimilar.Algebraic.integerMinimalPolynomial_resultant_ne_zero`
- `LpSelfSimilar.Algebraic.integerPolynomial_complex_eval`
- `LpSelfSimilar.Algebraic.one_le_abs_eval_mul_degree_mahler`
- `LpSelfSimilar.Algebraic.abs_eval_ge_inverse_degree_mahler`

### [Algebraic/SquaredConjugates](LpSelfSimilar/Algebraic/SquaredConjugates.lean)

- `LpSelfSimilar.Algebraic.rational_polynomial_coprime_reflection`
- `LpSelfSimilar.Algebraic.integer_polynomial_no_opposite_roots`
- `LpSelfSimilar.Algebraic.square_injOn_integer_polynomial_roots`
- `LpSelfSimilar.Algebraic.square_injOn_conjugates_of_not_even`

### [Algebraic/StrongDigitEntropy](LpSelfSimilar/Algebraic/StrongDigitEntropy.lean)

- `LpSelfSimilar.Algebraic.unit_digit_entropy_ge_binary_information`
- `LpSelfSimilar.Algebraic.unit_digit_entropy_three_tenths_lower`
- `LpSelfSimilar.Algebraic.unit_digit_entropy_half_lower`
- `LpSelfSimilar.Algebraic.digit_entropy_three_tenths_lower`
- `LpSelfSimilar.Algebraic.digit_entropy_half_lower`
- `LpSelfSimilar.Algebraic.digit_entropy_ge_algebraicEntropyLowerBound`
- `LpSelfSimilar.Algebraic.algebraicEntropyLowerBound_pos`
- `LpSelfSimilar.Algebraic.algebraicEntropyLowerBound_le_log_two`

### [Analysis/CancellationProfile](LpSelfSimilar/Analysis/CancellationProfile.lean)

- `LpSelfSimilar.Analysis.cancellationProfile_radicand_pos`
- `LpSelfSimilar.Analysis.hasDerivAt_cancellationProfile`
- `LpSelfSimilar.Analysis.hasDerivAt_cancellationProfileSlope`
- `LpSelfSimilar.Analysis.deriv_deriv_cancellationProfile`
- `LpSelfSimilar.Analysis.deriv_deriv_cancellationProfile_rpow`
- `LpSelfSimilar.Analysis.deriv_deriv_cancellationProfile_neg`
- `LpSelfSimilar.Analysis.concaveOn_cancellationProfile`
- `LpSelfSimilar.Analysis.cancellationProfile_three_fifths_chord`
- `LpSelfSimilar.Analysis.cancellationProfile_chord_coefficient_gt`

### [Analysis/CubicEndpointNumerics](LpSelfSimilar/Analysis/CubicEndpointNumerics.lean)

- `LpSelfSimilar.Analysis.log_eleven_bounds`
- `LpSelfSimilar.Analysis.log_eleven_thousand_lt`
- `LpSelfSimilar.Analysis.cubic_low_endpoint_margin`
- `LpSelfSimilar.Analysis.log_four_thousand_eight_hundred_lt`
- `LpSelfSimilar.Analysis.cubic_high_endpoint_margin`
- `LpSelfSimilar.Analysis.cubic_high_margin_lt_entropy_half`
- `LpSelfSimilar.Analysis.cubic_low_final_margin`

### [Analysis/CubicLogExclusions](LpSelfSimilar/Analysis/CubicLogExclusions.lean)

- `LpSelfSimilar.Analysis.concaveOn_three_log_sub_mul_add`
- `LpSelfSimilar.Analysis.three_log_sub_mul_add_pos_on_Icc`
- `LpSelfSimilar.Analysis.log_eight_eq_three_log_two`
- `LpSelfSimilar.Analysis.eight_lt_of_cubic_log_constraint`
- `LpSelfSimilar.Analysis.five_log_two_sub_log_three_lt_log_eleven`
- `LpSelfSimilar.Analysis.eleven_lt_of_cubic_log_constraint`

### [Analysis/CubicLogGap](LpSelfSimilar/Analysis/CubicLogGap.lean)

- `LpSelfSimilar.Analysis.cubic_gap_le_inverse_cube`
- `LpSelfSimilar.Analysis.cubic_gap_lt_one_div_512`
- `LpSelfSimilar.Analysis.cubic_squared_parameter_mem`
- `LpSelfSimilar.Analysis.squared_log_gap_le_gap_ratio`
- `LpSelfSimilar.Analysis.cubic_squared_log_gap_lt`
- `LpSelfSimilar.Analysis.cubic_squared_log_gap_lt_one_div_250`

### [Analysis/CubicLogRatios](LpSelfSimilar/Analysis/CubicLogRatios.lean)

- `LpSelfSimilar.Analysis.hasDerivAt_log_mul_div`
- `LpSelfSimilar.Analysis.antitoneOn_log_mul_div`
- `LpSelfSimilar.Analysis.log_mul_sq_div_cube_le`
- `LpSelfSimilar.Analysis.log_mul_sq_div_sq_log_le`
- `LpSelfSimilar.Analysis.one_le_log_of_three_le`
- `LpSelfSimilar.Analysis.cubic_high_log_ratio_le_endpoint`
- `LpSelfSimilar.Analysis.cubic_low_log_ratio_le_endpoint`

### [Analysis/CubicRationalThreshold](LpSelfSimilar/Analysis/CubicRationalThreshold.lean)

- `LpSelfSimilar.Analysis.hasDerivAt_cubicRationalAllowance`
- `LpSelfSimilar.Analysis.strictMonoOn_cubicRationalAllowance`
- `LpSelfSimilar.Analysis.cubicRationalAllowance_587_lt_one`
- `LpSelfSimilar.Analysis.one_lt_cubicRationalAllowance_588`
- `LpSelfSimilar.Analysis.cubicRationalAllowance_nat_lt_one_of_le_two`
- `LpSelfSimilar.Analysis.cubicRationalAllowance_integer_threshold`

### [Analysis/CubicScaleConstraints](LpSelfSimilar/Analysis/CubicScaleConstraints.lean)

- `LpSelfSimilar.Analysis.cubic_gap_log_lower_bound`
- `LpSelfSimilar.Analysis.degree_mahler_gap_cost_le`
- `LpSelfSimilar.Analysis.cubic_scale_eight_lt`
- `LpSelfSimilar.Analysis.cubic_small_mahler_gap_cost_lt`
- `LpSelfSimilar.Analysis.cubic_scale_eleven_lt`
- `LpSelfSimilar.Analysis.cubic_entropy_factor_lower_bound`

### [Analysis/CubicSmallness](LpSelfSimilar/Analysis/CubicSmallness.lean)

- `LpSelfSimilar.Analysis.cubic_high_branch_smallness`
- `LpSelfSimilar.Analysis.cubic_low_gap_log_ratio_le`
- `LpSelfSimilar.Analysis.cubic_low_gap_log_ratio_lt`
- `LpSelfSimilar.Analysis.cubic_low_branch_smallness`

### [Analysis/CubicThresholdNumerics](LpSelfSimilar/Analysis/CubicThresholdNumerics.lean)

- `LpSelfSimilar.Analysis.log_six_hundred_eq`
- `LpSelfSimilar.Analysis.log_587_gt`
- `LpSelfSimilar.Analysis.log_588_lt`
- `LpSelfSimilar.Analysis.cubic_denominator_587_gt`
- `LpSelfSimilar.Analysis.cubic_denominator_588_lt`

### [Analysis/DensityPowerTails](LpSelfSimilar/Analysis/DensityPowerTails.lean)

- `LpSelfSimilar.Analysis.rpow_bound_of_mass_inequality`
- `LpSelfSimilar.Analysis.density_superlevel_volume_mul_le_smallSetMass`
- `LpSelfSimilar.Analysis.density_superlevel_measure_ne_top`
- `LpSelfSimilar.Analysis.density_superlevel_volume_rpow_bound`

### [Analysis/FiniteLogCosineBounds](LpSelfSimilar/Analysis/FiniteLogCosineBounds.lean)

- `LpSelfSimilar.Analysis.exp_quartic_lower_le_prod_cos`
- `LpSelfSimilar.Analysis.sum_logCosineRemainder_eq_log_prod`
- `LpSelfSimilar.Analysis.sum_tan_remainder_eq_deriv_prod_div`

### [Analysis/GaussianConcentrationConstants](LpSelfSimilar/Analysis/GaussianConcentrationConstants.lean)

- `LpSelfSimilar.Analysis.one_le_gaussian_concentration_height`
- `LpSelfSimilar.Analysis.gaussian_concentration_budget_le_endpoint`
- `LpSelfSimilar.Analysis.gaussian_concentration_endpoint_lt_911_div_1000`
- `LpSelfSimilar.Analysis.rat_911_div_1000_lt_exp_neg_one_div_250`
- `LpSelfSimilar.Analysis.gaussian_concentration_budget_lt_parameter`

### [Analysis/GaussianEntropyProfile](LpSelfSimilar/Analysis/GaussianEntropyProfile.lean)

- `LpSelfSimilar.Analysis.continuous_gaussianEntropyProfile`
- `LpSelfSimilar.Analysis.gaussianEntropyProfile_zero`
- `LpSelfSimilar.Analysis.hasDerivAt_gaussianEntropyProfile`
- `LpSelfSimilar.Analysis.hasDerivAt_gaussianEntropyProfileSlope`
- `LpSelfSimilar.Analysis.deriv_deriv_gaussianEntropyProfile`
- `LpSelfSimilar.Analysis.gaussianEntropyProfileSlope_pos`
- `LpSelfSimilar.Analysis.strictMono_gaussianEntropyProfile`
- `LpSelfSimilar.Analysis.gaussianEntropyProfileCurvature_nonpos`
- `LpSelfSimilar.Analysis.concaveOn_gaussianEntropyProfile`
- `LpSelfSimilar.Analysis.gaussianEntropyProfile_one_mul_min_le`

### [Analysis/GaussianEntropyProfileConstants](LpSelfSimilar/Analysis/GaussianEntropyProfileConstants.lean)

- `LpSelfSimilar.Analysis.exp_neg_46_div_125_gt`
- `LpSelfSimilar.Analysis.exp_neg_1359_div_500_lt`
- `LpSelfSimilar.Analysis.gaussianEntropyProfile_one_gt`
- `LpSelfSimilar.Analysis.three_tenths_mul_min_le_gaussianEntropyProfile`

### [Analysis/GeometricLengthCutoff](LpSelfSimilar/Analysis/GeometricLengthCutoff.lean)

- `LpSelfSimilar.Analysis.geometricLengthCount_pos`
- `LpSelfSimilar.Analysis.geometricLengthCount_intCast`
- `LpSelfSimilar.Analysis.lt_geometricLengthCount_iff`
- `LpSelfSimilar.Analysis.ratio_lt_pow_geometricLengthCount`

### [Analysis/GeometricPhaseAverage](LpSelfSimilar/Analysis/GeometricPhaseAverage.lean)

- `LpSelfSimilar.Analysis.geometric_cosine_average_le`
- `LpSelfSimilar.Analysis.geometric_phase_average_gt_margin`
- `LpSelfSimilar.Analysis.geometric_phase_average_ge_three_fifths`
- `LpSelfSimilar.Analysis.geometric_phase_average_ge_of_log_gap`

### [Analysis/GeometricPhaseConstants](LpSelfSimilar/Analysis/GeometricPhaseConstants.lean)

- `LpSelfSimilar.Analysis.exp_neg_one_seventieth_gt`
- `LpSelfSimilar.Analysis.geometric_phase_margin_gt`

### [Analysis/GeometricPhaseLength](LpSelfSimilar/Analysis/GeometricPhaseLength.lean)

- `LpSelfSimilar.Analysis.pow_geometricPhaseLength_le`

### [Analysis/GeometricQuadratureTail](LpSelfSimilar/Analysis/GeometricQuadratureTail.lean)

- `LpSelfSimilar.Analysis.abs_tail_endpoint_error_le`
- `LpSelfSimilar.Analysis.abs_geometric_average_sub_integral_le`

### [Analysis/LargeMassCancellation](LpSelfSimilar/Analysis/LargeMassCancellation.lean)

- `LpSelfSimilar.Analysis.one_sub_sqrt_div_eq`
- `LpSelfSimilar.Analysis.large_mass_cancellation_ratio_lower`
- `LpSelfSimilar.Analysis.large_mass_cancellation_ratio`
- `LpSelfSimilar.Analysis.large_mass_cancellation_thirteen_fortieths`

### [Analysis/LogCosineRemainder](LpSelfSimilar/Analysis/LogCosineRemainder.lean)

- `LpSelfSimilar.Analysis.half_le_cos_of_abs_le_one`
- `LpSelfSimilar.Analysis.sin_sub_mul_cos_le_cube_div_three`
- `LpSelfSimilar.Analysis.tan_sub_self_bounds_of_nonneg_le_one`
- `LpSelfSimilar.Analysis.hasDerivAt_logCosineRemainder`
- `LpSelfSimilar.Analysis.logCosineRemainder_bounds_of_nonneg_le_one`
- `LpSelfSimilar.Analysis.logCosineRemainder_neg`
- `LpSelfSimilar.Analysis.logCosineRemainder_bounds`
- `LpSelfSimilar.Analysis.abs_tan_sub_self_le_two_thirds_abs_cube`

### [Analysis/MassDecayExponent](LpSelfSimilar/Analysis/MassDecayExponent.lean)

- `LpSelfSimilar.Analysis.massDecayExponent_pos`
- `LpSelfSimilar.Analysis.massDecayExponent_lt_one_iff`
- `LpSelfSimilar.Analysis.half_lt_massDecayExponent_iff`
- `LpSelfSimilar.Analysis.rpow_massDecayExponent`
- `LpSelfSimilar.Analysis.geometric_volume_rpow_massDecayExponent`

### [Analysis/PackingNumericalBounds](LpSelfSimilar/Analysis/PackingNumericalBounds.lean)

- `LpSelfSimilar.Analysis.six_lt_log_four_hundred_fifty`
- `LpSelfSimilar.Analysis.log_ten_thousand_lt_ten`
- `LpSelfSimilar.Analysis.packing_cancellation_margin_gt`

### [Analysis/SmallSetMassPowers](LpSelfSimilar/Analysis/SmallSetMassPowers.lean)

- `LpSelfSimilar.Analysis.smallSetMass_le_rpow_of_geometric`
- `LpSelfSimilar.Analysis.smallSetMass_le_rpow_of_recurrence`

### [Analysis/SquareLayerCake](LpSelfSimilar/Analysis/SquareLayerCake.lean)

- `LpSelfSimilar.Analysis.integral_twice_id_zero`
- `LpSelfSimilar.Analysis.lintegral_sq_eq_twice_lintegral_superlevel`

### [Bernoulli/ConditionalTailInversion](LpSelfSimilar/Bernoulli/ConditionalTailInversion.lean)

- `LpSelfSimilar.Bernoulli.integral_inverse_normalized_blocks_reserved_tail_le`

### [Bernoulli/Construction](LpSelfSimilar/Bernoulli/Construction.lean)

- `LpSelfSimilar.Bernoulli.fairDigit_eq`
- `LpSelfSimilar.Bernoulli.measurable_sign`
- `LpSelfSimilar.Bernoulli.measurable_series`
- `LpSelfSimilar.Bernoulli.independent_digits`
- `LpSelfSimilar.Bernoulli.digit_law`
- `LpSelfSimilar.Bernoulli.subsequence_law`
- `LpSelfSimilar.Bernoulli.series_subsequence_law`
- `LpSelfSimilar.Bernoulli.convolution_compl_interval`

### [Bernoulli/ContinuousDensity](LpSelfSimilar/Bernoulli/ContinuousDensity.lean)

- `LpSelfSimilar.Bernoulli.continuous_density_of_power_memLp`

### [Bernoulli/ConvolutionPowers](LpSelfSimilar/Bernoulli/ConvolutionPowers.lean)

- `LpSelfSimilar.Bernoulli.convolution_eq_finiteConvolution_power`

### [Bernoulli/DetailSmoothingEstimate](LpSelfSimilar/Bernoulli/DetailSmoothingEstimate.lean)

- `LpSelfSimilar.Bernoulli.smoothingLengthCount_of_lt`
- `LpSelfSimilar.Bernoulli.smoothingLengthCount_of_le`
- `LpSelfSimilar.Bernoulli.bernoulli_detail_smoothing_bound`

### [Bernoulli/DigitBandBlock](LpSelfSimilar/Bernoulli/DigitBandBlock.lean)

- `LpSelfSimilar.Bernoulli.digitBandShiftedLaw_univ`
- `LpSelfSimilar.Bernoulli.digitPMF_eq_band_mixture`
- `LpSelfSimilar.Bernoulli.digitBandShiftedLaw_charFun_norm_average`
- `LpSelfSimilar.Bernoulli.exists_digit_band_block`

### [Bernoulli/DigitBandEntropy](LpSelfSimilar/Bernoulli/DigitBandEntropy.lean)

- `LpSelfSimilar.Bernoulli.digit_band_entropy_integral_lower_bound`
- `LpSelfSimilar.Bernoulli.digit_band_entropy_integral_lower_bound_explicit`

### [Bernoulli/DigitEntropySubadditivity](LpSelfSimilar/Bernoulli/DigitEntropySubadditivity.lean)

- `LpSelfSimilar.Bernoulli.digitEntropy_nonneg`
- `LpSelfSimilar.Bernoulli.digitEntropy_le_length_log_two`
- `LpSelfSimilar.Bernoulli.digitEntropy_zero`
- `LpSelfSimilar.Bernoulli.digitEntropy_subadditive`
- `LpSelfSimilar.Bernoulli.digitEntropy_div_nonneg`

### [Bernoulli/Digits](LpSelfSimilar/Bernoulli/Digits.lean)

- `LpSelfSimilar.Bernoulli.sign_false`
- `LpSelfSimilar.Bernoulli.sign_true`
- `LpSelfSimilar.Bernoulli.abs_sign`
- `LpSelfSimilar.Bernoulli.norm_sign`
- `LpSelfSimilar.Bernoulli.digitSum_eq_two_mul_bitSum_sub`
- `LpSelfSimilar.Bernoulli.bitSum_zero`
- `LpSelfSimilar.Bernoulli.bitSum_succ`
- `LpSelfSimilar.Bernoulli.summable_sign_mul_pow`
- `LpSelfSimilar.Bernoulli.abs_series_le`
- `LpSelfSimilar.Bernoulli.series_eq_head_add_tail`

### [Bernoulli/EntropyRate](LpSelfSimilar/Bernoulli/EntropyRate.lean)

- `LpSelfSimilar.Bernoulli.digitEntropy_div_bddBelow`
- `LpSelfSimilar.Bernoulli.entropyRate_eq_sInf`
- `LpSelfSimilar.Bernoulli.tendsto_digitEntropy_div`
- `LpSelfSimilar.Bernoulli.entropyRate_nonneg`
- `LpSelfSimilar.Bernoulli.entropyRate_le_log_two`
- `LpSelfSimilar.Bernoulli.mul_entropyRate_le_digitEntropy`
- `LpSelfSimilar.Bernoulli.le_entropyRate_of_mul_le`
- `LpSelfSimilar.Bernoulli.entropyRate_eq_of_digitEntropy_eq`

### [Bernoulli/GaussianApproximation](LpSelfSimilar/Bernoulli/GaussianApproximation.lean)

- `LpSelfSimilar.Bernoulli.integral_abs_original_packing_smoothedGaussianError_lt`
- `LpSelfSimilar.Bernoulli.bernoulli_exists_density_with_gaussian_error`

### [Bernoulli/GaussianApproximationL2](LpSelfSimilar/Bernoulli/GaussianApproximationL2.lean)

- `LpSelfSimilar.Bernoulli.bernoulli_density_memLp_two_of_gaussian_error`

### [Bernoulli/GaussianApproximationMassBound](LpSelfSimilar/Bernoulli/GaussianApproximationMassBound.lean)

- `LpSelfSimilar.Bernoulli.convolution_small_set_bound_of_gaussian_error`
- `LpSelfSimilar.Bernoulli.unitIntervalNormalization_small_set_bound_of_gaussian_error`

### [Bernoulli/GaussianHighFrequencyMargin](LpSelfSimilar/Bernoulli/GaussianHighFrequencyMargin.lean)

- `LpSelfSimilar.Bernoulli.sqrt_highFrequency_standardGaussian_energy_lt`

### [Bernoulli/HighFrequencyEnergy](LpSelfSimilar/Bernoulli/HighFrequencyEnergy.lean)

- `LpSelfSimilar.Bernoulli.highFrequency_smoothed_fourier_energy_bound`

### [Bernoulli/HighFrequencyEnergyMargin](LpSelfSimilar/Bernoulli/HighFrequencyEnergyMargin.lean)

- `LpSelfSimilar.Bernoulli.sqrt_highFrequency_packing_smoothing_energy_lt`

### [Bernoulli/HighFrequencyParameters](LpSelfSimilar/Bernoulli/HighFrequencyParameters.lean)

- `LpSelfSimilar.Bernoulli.inv_parameter_le_one_point_zero_one`
- `LpSelfSimilar.Bernoulli.exists_normalized_small_angle_tail`
- `LpSelfSimilar.Bernoulli.normalized_coefficient_sum_lt_three_halves`

### [Bernoulli/HighFrequencyTailBounds](LpSelfSimilar/Bernoulli/HighFrequencyTailBounds.lean)

- `LpSelfSimilar.Bernoulli.norm_charFun_scaled_convolution_le_tail_gaussian`
- `LpSelfSimilar.Bernoulli.norm_deriv_charFun_scaled_convolution_le_tail_gaussian`

### [Bernoulli/IntegratedDetailEnvelope](LpSelfSimilar/Bernoulli/IntegratedDetailEnvelope.lean)

- `LpSelfSimilar.Bernoulli.integratedDetailEnvelope_eq`
- `LpSelfSimilar.Bernoulli.integratedDetailEnvelope_pos`
- `LpSelfSimilar.Bernoulli.sqrt_two_hundred_fifty_le_inv_sqrt`
- `LpSelfSimilar.Bernoulli.strictMonoOn_integratedDetailEnvelope`

### [Bernoulli/IntegratedEnvelopeComparison](LpSelfSimilar/Bernoulli/IntegratedEnvelopeComparison.lean)

- `LpSelfSimilar.Bernoulli.ratio_eq_exp_packingLogScale_div`
- `LpSelfSimilar.Bernoulli.packingLogScale_le_inverse_sqrt_gap`
- `LpSelfSimilar.Bernoulli.integrated_coefficient_le_envelope`

### [Bernoulli/IntegratedEnvelopeDerivative](LpSelfSimilar/Bernoulli/IntegratedEnvelopeDerivative.lean)

- `LpSelfSimilar.Bernoulli.hasDerivAt_log_integratedDetailEnvelope`
- `LpSelfSimilar.Bernoulli.hasDerivAt_logarithmic_integratedDetailEnvelope`
- `LpSelfSimilar.Bernoulli.integratedDetailEnvelopeLogSlope_lower_bound`
- `LpSelfSimilar.Bernoulli.integratedDetailEnvelope_logSlope_lower_pos`

### [Bernoulli/IntegratedEnvelopeSmallness](LpSelfSimilar/Bernoulli/IntegratedEnvelopeSmallness.lean)

- `LpSelfSimilar.Bernoulli.integratedDetailEnvelope_endpoint_lt`
- `LpSelfSimilar.Bernoulli.integratedDetailEnvelope_uniform_endpoint_bound`
- `LpSelfSimilar.Bernoulli.integratedDetailEnvelope_lt_one_hundredth`

### [Bernoulli/IntegratedLogarithmicDetail](LpSelfSimilar/Bernoulli/IntegratedLogarithmicDetail.lean)

- `LpSelfSimilar.Bernoulli.bernoulli_detail_logarithmic_integral_bound`

### [Bernoulli/LogarithmicRemainder](LpSelfSimilar/Bernoulli/LogarithmicRemainder.lean)

- `LpSelfSimilar.Bernoulli.hasDerivAt_varianceNormalizedLogRemainder`
- `LpSelfSimilar.Bernoulli.varianceNormalizedFourier_eq_gaussian_remainder`
- `LpSelfSimilar.Bernoulli.varianceNormalizedLogRemainder_bounds`
- `LpSelfSimilar.Bernoulli.tendsto_sum_logCosineRemainder`
- `LpSelfSimilar.Bernoulli.hasSum_logCosineRemainder`
- `LpSelfSimilar.Bernoulli.varianceNormalizedLogRemainder_neg`
- `LpSelfSimilar.Bernoulli.varianceNormalizedLogRemainder_zero`

### [Bernoulli/LogarithmicRemainderDerivative](LpSelfSimilar/Bernoulli/LogarithmicRemainderDerivative.lean)

- `LpSelfSimilar.Bernoulli.tendsto_sum_tan_remainder`
- `LpSelfSimilar.Bernoulli.abs_deriv_varianceNormalizedLogRemainder_le`
- `LpSelfSimilar.Bernoulli.summable_tan_remainder`
- `LpSelfSimilar.Bernoulli.hasSum_tan_remainder`

### [Bernoulli/LowFrequencyEnergy](LpSelfSimilar/Bernoulli/LowFrequencyEnergy.lean)

- `LpSelfSimilar.Bernoulli.half_integral_lowFrequency_charFun_error_le`
- `LpSelfSimilar.Bernoulli.sqrt_half_integral_lowFrequency_charFun_error_lt`

### [Bernoulli/LowFrequencyGaussianApproximation](LpSelfSimilar/Bernoulli/LowFrequencyGaussianApproximation.lean)

- `LpSelfSimilar.Bernoulli.tendsto_varianceNormalized_cosine_products`
- `LpSelfSimilar.Bernoulli.tendsto_varianceNormalized_gaussians`
- `LpSelfSimilar.Bernoulli.norm_charFun_varianceNormalized_sub_gaussian_le`

### [Bernoulli/LowFrequencyGaussianDerivative](LpSelfSimilar/Bernoulli/LowFrequencyGaussianDerivative.lean)

- `LpSelfSimilar.Bernoulli.sum_sq_varianceNormalizedCoefficient_le_one`
- `LpSelfSimilar.Bernoulli.tendsto_deriv_varianceNormalized_cosine_products`
- `LpSelfSimilar.Bernoulli.norm_deriv_charFun_varianceNormalized_add_gaussian_le`

### [Bernoulli/NormalizedGaussianHeight](LpSelfSimilar/Bernoulli/NormalizedGaussianHeight.lean)

- `LpSelfSimilar.Bernoulli.normalizedGaussianPeak_pos`
- `LpSelfSimilar.Bernoulli.normalizedGaussianPeak_sq`
- `LpSelfSimilar.Bernoulli.normalizedGaussianPeak_eq`
- `LpSelfSimilar.Bernoulli.normalized_gaussian_density_le_peak`
- `LpSelfSimilar.Bernoulli.normalized_gaussian_density_at_half`
- `LpSelfSimilar.Bernoulli.log_gap_mul_normalizedGaussianPeak_sq_le`
- `LpSelfSimilar.Bernoulli.normalized_gaussian_peak_square_margin`
- `LpSelfSimilar.Bernoulli.normalizedGaussianPeak_le_concentration_height`

### [Bernoulli/PackingAttenuation](LpSelfSimilar/Bernoulli/PackingAttenuation.lean)

- `LpSelfSimilar.Bernoulli.packingAttenuation_lower_bound`
- `LpSelfSimilar.Bernoulli.packingLogScale_lt_attenuation`
- `LpSelfSimilar.Bernoulli.packingLengthMultiplier_mul_exp_neg_attenuation_le`

### [Bernoulli/PackingConditionalDecomposition](LpSelfSimilar/Bernoulli/PackingConditionalDecomposition.lean)

- `LpSelfSimilar.Bernoulli.exists_packing_conditional_decomposition`

### [Bernoulli/PackingDerivativeBounds](LpSelfSimilar/Bernoulli/PackingDerivativeBounds.lean)

- `LpSelfSimilar.Bernoulli.exists_packing_normalized_derivative_bounds`

### [Bernoulli/PackingEndpointError](LpSelfSimilar/Bernoulli/PackingEndpointError.lean)

- `LpSelfSimilar.Bernoulli.packing_cancellationSlope_one_le`
- `LpSelfSimilar.Bernoulli.packing_cancellationRemainder_le_one`
- `LpSelfSimilar.Bernoulli.packing_entropy_endpoint_error_lt`

### [Bernoulli/PackingGaussianWidth](LpSelfSimilar/Bernoulli/PackingGaussianWidth.lean)

- `LpSelfSimilar.Bernoulli.packing_ratio_eq_exp_logScale`
- `LpSelfSimilar.Bernoulli.inv_packingFrequencyWidth_eq`
- `LpSelfSimilar.Bernoulli.packingLogScale_le_inv_sqrt`
- `LpSelfSimilar.Bernoulli.inv_packingFrequencyWidth_le_gaussian`

### [Bernoulli/PackingGridBudget](LpSelfSimilar/Bernoulli/PackingGridBudget.lean)

- `LpSelfSimilar.Bernoulli.packing_grid_attenuation_budget`
- `LpSelfSimilar.Bernoulli.packing_grid_budget_with_endpoint`

### [Bernoulli/PackingGridCount](LpSelfSimilar/Bernoulli/PackingGridCount.lean)

- `LpSelfSimilar.Bernoulli.packingGridSpacing_pos`
- `LpSelfSimilar.Bernoulli.packingGridCandidateCount_covers`
- `LpSelfSimilar.Bernoulli.packingGridCandidateCount_le`

### [Bernoulli/PackingGridSelection](LpSelfSimilar/Bernoulli/PackingGridSelection.lean)

- `LpSelfSimilar.Bernoulli.exists_packing_grid`
- `LpSelfSimilar.Bernoulli.exists_retained_packing_grid`

### [Bernoulli/PackingLengthSeparation](LpSelfSimilar/Bernoulli/PackingLengthSeparation.lean)

- `LpSelfSimilar.Bernoulli.packingBaseLength_entropy_mul_gt`
- `LpSelfSimilar.Bernoulli.packing_dyadic_gap_lt`
- `LpSelfSimilar.Bernoulli.packingLengthMultiplier_window_slope_gt`
- `LpSelfSimilar.Bernoulli.packing_length_padding_margin`
- `LpSelfSimilar.Bernoulli.packing_window_lower_gt_two`
- `LpSelfSimilar.Bernoulli.packing_length_windows_separated`

### [Bernoulli/PackingLengths](LpSelfSimilar/Bernoulli/PackingLengths.lean)

- `LpSelfSimilar.Bernoulli.packingScaleThreshold_pos`
- `LpSelfSimilar.Bernoulli.packingLengthCount_pos`
- `LpSelfSimilar.Bernoulli.packingLengthCount_intCast`
- `LpSelfSimilar.Bernoulli.packingBaseLength_le_blockLength`
- `LpSelfSimilar.Bernoulli.packingBlockLength_pos`
- `LpSelfSimilar.Bernoulli.packingBlockLength_step_le`
- `LpSelfSimilar.Bernoulli.lt_packingLengthCount_iff`

### [Bernoulli/PackingNaturalBlocks](LpSelfSimilar/Bernoulli/PackingNaturalBlocks.lean)

- `LpSelfSimilar.Bernoulli.exists_packing_natural_blocks`

### [Bernoulli/PackingPadding](LpSelfSimilar/Bernoulli/PackingPadding.lean)

- `LpSelfSimilar.Bernoulli.packing_phase_padding_ratio_bounds`
- `LpSelfSimilar.Bernoulli.packing_frequency_width_mul_length`
- `LpSelfSimilar.Bernoulli.packing_endpoint_loss_le`
- `LpSelfSimilar.Bernoulli.packing_endpoint_loss_lt`

### [Bernoulli/PackingParameters](LpSelfSimilar/Bernoulli/PackingParameters.lean)

- `LpSelfSimilar.Bernoulli.six_lt_packingLogScale`
- `LpSelfSimilar.Bernoulli.packingFrequencyWidth_pos`
- `LpSelfSimilar.Bernoulli.packingFrequencyWidth_lt`
- `LpSelfSimilar.Bernoulli.packingLengthMultiplier_bounds`
- `LpSelfSimilar.Bernoulli.twenty_seven_le_packingLengthMultiplier`
- `LpSelfSimilar.Bernoulli.packingBaseLength_lower_bound`
- `LpSelfSimilar.Bernoulli.packingBaseLength_pos`
- `LpSelfSimilar.Bernoulli.packing_gap_div_entropy_lt`

### [Bernoulli/PackingSmoothingEstimate](LpSelfSimilar/Bernoulli/PackingSmoothingEstimate.lean)

- `LpSelfSimilar.Bernoulli.packing_smoothing_bound`

### [Bernoulli/PackingThresholdUpperBound](LpSelfSimilar/Bernoulli/PackingThresholdUpperBound.lean)

- `LpSelfSimilar.Bernoulli.packingBaseLength_upper_bound`
- `LpSelfSimilar.Bernoulli.packingScaleThreshold_upper_bound`
- `LpSelfSimilar.Bernoulli.smoothingPrefactor_mul_threshold_div_gap_le`

### [Bernoulli/ReservedTailAngles](LpSelfSimilar/Bernoulli/ReservedTailAngles.lean)

- `LpSelfSimilar.Bernoulli.reserved_tail_angle_ratio_lt`
- `LpSelfSimilar.Bernoulli.reservedTailStart_angle_bounds`
- `LpSelfSimilar.Bernoulli.reservedTailStart_coordinate_lt_two`

### [Bernoulli/ReservedTailCoefficients](LpSelfSimilar/Bernoulli/ReservedTailCoefficients.lean)

- `LpSelfSimilar.Bernoulli.hasSum_tail_coefficients`
- `LpSelfSimilar.Bernoulli.reservedTailStart_coefficient_sum_lt`

### [Bernoulli/ReservedTailDerivatives](LpSelfSimilar/Bernoulli/ReservedTailDerivatives.lean)

- `LpSelfSimilar.Bernoulli.norm_iteratedDeriv_charFun_scaled_convolution_le_gaussian`
- `LpSelfSimilar.Bernoulli.norm_iteratedDeriv_charFun_reserved_tail_le`
- `LpSelfSimilar.Bernoulli.norm_iteratedDeriv_reserved_tail_fourier_le`

### [Bernoulli/ReservedTailFourier](LpSelfSimilar/Bernoulli/ReservedTailFourier.lean)

- `LpSelfSimilar.Bernoulli.norm_charFun_convolution_le_gaussian`
- `LpSelfSimilar.Bernoulli.norm_charFun_reserved_tail_le`

### [Bernoulli/ReservedTailIndex](LpSelfSimilar/Bernoulli/ReservedTailIndex.lean)

- `LpSelfSimilar.Bernoulli.reserved_tail_parameter_lower`
- `LpSelfSimilar.Bernoulli.reserved_tail_upperEndpoint_bounds`
- `LpSelfSimilar.Bernoulli.reservedTailStart_intCast`
- `LpSelfSimilar.Bernoulli.reservedTailStart_spec`

### [Bernoulli/ReservedTailProductDerivatives](LpSelfSimilar/Bernoulli/ReservedTailProductDerivatives.lean)

- `LpSelfSimilar.Bernoulli.packing_total_derivative_cost_le`
- `LpSelfSimilar.Bernoulli.integral_norm_iteratedDeriv_mul_reserved_tail_le`

### [Bernoulli/ReservedTailSmoothing](LpSelfSimilar/Bernoulli/ReservedTailSmoothing.lean)

- `LpSelfSimilar.Bernoulli.reserved_tail_smoothing_bound`

### [Bernoulli/ResidueLaw](LpSelfSimilar/Bernoulli/ResidueLaw.lean)

- `LpSelfSimilar.Bernoulli.residue_streams_law`
- `LpSelfSimilar.Bernoulli.independent_residue_streams`
- `LpSelfSimilar.Bernoulli.independent_residue_series`
- `LpSelfSimilar.Bernoulli.scaled_residue_series_law`

### [Bernoulli/Residues](LpSelfSimilar/Bernoulli/Residues.lean)

- `LpSelfSimilar.Bernoulli.series_split_residues`

### [Bernoulli/SmoothedGaussianApproximation](LpSelfSimilar/Bernoulli/SmoothedGaussianApproximation.lean)

- `LpSelfSimilar.Bernoulli.integral_abs_packing_smoothedGaussianError_lt`

### [Bernoulli/SmoothedGaussianPlancherel](LpSelfSimilar/Bernoulli/SmoothedGaussianPlancherel.lean)

- `LpSelfSimilar.Bernoulli.integrable_smoothedGaussianError`
- `LpSelfSimilar.Bernoulli.smoothedGaussian_weighted_L1_bound`

### [Bernoulli/SmoothingDensity](LpSelfSimilar/Bernoulli/SmoothingDensity.lean)

- `LpSelfSimilar.Bernoulli.bernoulli_exists_density_with_smoothing_error`

### [Bernoulli/UnitIntervalNormalization](LpSelfSimilar/Bernoulli/UnitIntervalNormalization.lean)

- `LpSelfSimilar.Bernoulli.unitIntervalNormalization_apply`
- `LpSelfSimilar.Bernoulli.unitIntervalNormalization_mem_unitInterval`
- `LpSelfSimilar.Bernoulli.unitIntervalNormalization_convolution_compl_unitInterval`
- `LpSelfSimilar.Bernoulli.unitIntervalNormalization_conjugates_digit`
- `LpSelfSimilar.Bernoulli.unitIntervalNormalization_convolution_stationary`

### [Bernoulli/VarianceNormalization](LpSelfSimilar/Bernoulli/VarianceNormalization.lean)

- `LpSelfSimilar.Bernoulli.integral_id_scaled_convolution_eq_zero`
- `LpSelfSimilar.Bernoulli.integral_sq_scaled_convolution`
- `LpSelfSimilar.Bernoulli.variance_id_scaled_convolution`
- `LpSelfSimilar.Bernoulli.integral_sq_varianceNormalized_convolution_eq_one`
- `LpSelfSimilar.Bernoulli.variance_id_varianceNormalized_convolution_eq_one`

### [Bernoulli/VarianceNormalizedCoefficients](LpSelfSimilar/Bernoulli/VarianceNormalizedCoefficients.lean)

- `LpSelfSimilar.Bernoulli.variance_scale_pos`
- `LpSelfSimilar.Bernoulli.varianceNormalizedCoefficient_nonneg`
- `LpSelfSimilar.Bernoulli.varianceNormalizedCoefficient_le_sqrt`
- `LpSelfSimilar.Bernoulli.hasSum_varianceNormalizedCoefficient`
- `LpSelfSimilar.Bernoulli.hasSum_sq_varianceNormalizedCoefficient`
- `LpSelfSimilar.Bernoulli.hasSum_fourth_varianceNormalizedCoefficient`
- `LpSelfSimilar.Bernoulli.tsum_fourth_varianceNormalizedCoefficient_eq_tanh`
- `LpSelfSimilar.Bernoulli.tsum_fourth_varianceNormalizedCoefficient_le_gap`

### [Bernoulli/VarianceNormalizedSums](LpSelfSimilar/Bernoulli/VarianceNormalizedSums.lean)

- `LpSelfSimilar.Bernoulli.sum_fourth_varianceNormalizedCoefficient_le_gap`
- `LpSelfSimilar.Bernoulli.tendsto_sum_sq_varianceNormalizedCoefficient`
- `LpSelfSimilar.Bernoulli.abs_varianceNormalizedCoefficient_mul_le_one`

### [Bernoulli/WorkingRegularityCriterion](LpSelfSimilar/Bernoulli/WorkingRegularityCriterion.lean)

- `LpSelfSimilar.Bernoulli.working_regularity_criterion`

### [Entropy/BinaryDecoderBounds](LpSelfSimilar/Entropy/BinaryDecoderBounds.lean)

- `LpSelfSimilar.Entropy.binEntropy_one_div_thirty_two_le`
- `LpSelfSimilar.Entropy.binEntropy_le_of_le_one_div_thirty_two`
- `LpSelfSimilar.Entropy.exp_neg_four_lt`
- `LpSelfSimilar.Entropy.binary_decoder_information_margin`

### [Entropy/BinaryVariational](LpSelfSimilar/Entropy/BinaryVariational.lean)

- `LpSelfSimilar.Entropy.binEntropy_add_mul_le_log_one_add_exp`
- `LpSelfSimilar.Entropy.binary_variational_maximizer_mem`
- `LpSelfSimilar.Entropy.binEntropy_variational_maximizer_value`
- `LpSelfSimilar.Entropy.binEntropy_variational_isGreatest`
- `LpSelfSimilar.Entropy.binEntropy_variational_sup`
- `LpSelfSimilar.Entropy.binary_entropy_sixteen_variational_bound`

### [Entropy/CancellationParameters](LpSelfSimilar/Entropy/CancellationParameters.lean)

- `LpSelfSimilar.Entropy.cancellationSlope_pos`
- `LpSelfSimilar.Entropy.cancellation_remainder_at_slope`
- `LpSelfSimilar.Entropy.cancellationRemainder_nonneg`
- `LpSelfSimilar.Entropy.cancellationRemainder_le`

### [Entropy/CancellationRate](LpSelfSimilar/Entropy/CancellationRate.lean)

- `LpSelfSimilar.Entropy.three_le_separation_entropy_ratio`
- `LpSelfSimilar.Entropy.bandCancellationRate_lower_bound`

### [Entropy/DifferentialEntropy](LpSelfSimilar/Entropy/DifferentialEntropy.lean)

- `LpSelfSimilar.Entropy.log_rnDeriv_eq_log_density`
- `LpSelfSimilar.Entropy.integrable_log_rnDeriv_of_density`
- `LpSelfSimilar.Entropy.differentialEntropy_eq_neg_integral_log_density`
- `LpSelfSimilar.Entropy.integrable_log_density_iff`
- `LpSelfSimilar.Entropy.differentialEntropy_eq_neg_integral_density_mul_log`

### [Entropy/DistanceBandDecomposition](LpSelfSimilar/Entropy/DistanceBandDecomposition.lean)

- `LpSelfSimilar.Entropy.exists_distanceBand_decomposition`

### [Entropy/DistanceBandEntropyBudget](LpSelfSimilar/Entropy/DistanceBandEntropyBudget.lean)

- `LpSelfSimilar.Entropy.distanceBand_integral_ge_quantized_entropy`
- `LpSelfSimilar.Entropy.distanceBand_integrated_entropy_budget`

### [Entropy/DistanceBandGraph](LpSelfSimilar/Entropy/DistanceBandGraph.lean)

- `LpSelfSimilar.Entropy.distanceBandGraph_compl_eq_sup`
- `LpSelfSimilar.Entropy.entropy_sub_band_compl_ge_near_difference`
- `LpSelfSimilar.Entropy.distanceBandGraph_clique_card_le_sixteen`

### [Entropy/DistanceBandScaleBudget](LpSelfSimilar/Entropy/DistanceBandScaleBudget.lean)

- `LpSelfSimilar.Entropy.intervalIntegrable_function_of_finite_graph`
- `LpSelfSimilar.Entropy.measurable_dyadic_distanceBandConditionalEntropyBits`
- `LpSelfSimilar.Entropy.intervalIntegrable_dyadic_distanceBandConditionalEntropyBits`
- `LpSelfSimilar.Entropy.four_mul_near_entropy_le_distanceBand_integral`

### [Entropy/DistanceGraphDuality](LpSelfSimilar/Entropy/DistanceGraphDuality.lean)

- `LpSelfSimilar.Entropy.nearDistanceGraph_eq_incomparabilityGraph`
- `LpSelfSimilar.Entropy.graphEntropy_nearDistance_add_compl`

### [Entropy/DominantAtomGrouping](LpSelfSimilar/Entropy/DominantAtomGrouping.lean)

- `LpSelfSimilar.Entropy.finite_entropy_mass_bound`
- `LpSelfSimilar.Entropy.finite_entropy_le_binary_grouping`
- `LpSelfSimilar.Entropy.sixteen_atom_entropy_le_binary_grouping`

### [Entropy/ExplicitCancellationBudget](LpSelfSimilar/Entropy/ExplicitCancellationBudget.lean)

- `LpSelfSimilar.Entropy.MaximizingBandFamily.cancellation_integral_lower_bound_explicit`

### [Entropy/FiniteCancellation](LpSelfSimilar/Entropy/FiniteCancellation.lean)

- `LpSelfSimilar.Entropy.cancellation_ge_thirteen_fortieths`
- `LpSelfSimilar.Entropy.finite_cancellation_ge_mass_outside_max`

### [Entropy/FiniteCoverInformation](LpSelfSimilar/Entropy/FiniteCoverInformation.lean)

- `LpSelfSimilar.Entropy.finite_entropy_le_coverage_cost_add`
- `LpSelfSimilar.Entropy.negMulLog_finiteCoverJoint`
- `LpSelfSimilar.Entropy.finiteCover_joint_entropy_eq`
- `LpSelfSimilar.Entropy.finiteCover_joint_sub_label_entropy_ge`

### [Entropy/FiniteLawBandEntropy](LpSelfSimilar/Entropy/FiniteLawBandEntropy.lean)

- `LpSelfSimilar.Entropy.finiteLawBandEntropy_integral_lower_bound`

### [Entropy/GraphComplement](LpSelfSimilar/Entropy/GraphComplement.lean)

- `LpSelfSimilar.Entropy.independentSetPolytope_sum_le`
- `LpSelfSimilar.Entropy.independentSetPolytope_compl_dot_le_one`
- `LpSelfSimilar.Entropy.finite_entropy_le_coverage_cost_add_on_support`
- `LpSelfSimilar.Entropy.entropy_le_graphEntropy_add_compl`

### [Entropy/GraphConditionalDecomposition](LpSelfSimilar/Entropy/GraphConditionalDecomposition.lean)

- `LpSelfSimilar.Entropy.exists_graph_conditional_decomposition`

### [Entropy/GraphConditionalVariational](LpSelfSimilar/Entropy/GraphConditionalVariational.lean)

- `LpSelfSimilar.Entropy.jointConditionalEntropy_le_entropy_sub_graphEntropy`
- `LpSelfSimilar.Entropy.graphConditionalEntropy_eq_entropy_sub_graphEntropy`
- `LpSelfSimilar.Entropy.jointConditionalEntropy_le_canonical_maximum`

### [Entropy/GraphEntropy](LpSelfSimilar/Entropy/GraphEntropy.lean)

- `LpSelfSimilar.Entropy.graphCoverageCost_nonneg`
- `LpSelfSimilar.Entropy.exists_graphEntropy_minimizer`
- `LpSelfSimilar.Entropy.graphEntropy_nonneg`
- `LpSelfSimilar.Entropy.graphEntropy_minimizer_independent_set_bound`

### [Entropy/GraphSeparationScale](LpSelfSimilar/Entropy/GraphSeparationScale.lean)

- `LpSelfSimilar.Entropy.nearDistanceGraph_eq_bot_of_separated`
- `LpSelfSimilar.Entropy.dyadic_near_graphEntropyBits_eq_zero_of_separated`

### [Entropy/GraphUnion](LpSelfSimilar/Entropy/GraphUnion.lean)

- `LpSelfSimilar.Entropy.independentSetPolytope_mul_mem_sup`
- `LpSelfSimilar.Entropy.graphCoverageCost_mul_eq_add`
- `LpSelfSimilar.Entropy.graphEntropy_sup_le_add`

### [Entropy/JointCancellationBounds](LpSelfSimilar/Entropy/JointCancellationBounds.lean)

- `LpSelfSimilar.Entropy.supportedJoint_sum_conditional_on_cover`
- `LpSelfSimilar.Entropy.supportedJoint_conditionalCancellation_eq`
- `LpSelfSimilar.Entropy.jointExpectedCancellation_nonneg`
- `LpSelfSimilar.Entropy.jointExpectedCancellation_le_sixteen_atom_bound`
- `LpSelfSimilar.Entropy.measurable_jointExpectedCancellation`

### [Entropy/MeasurableBandConditionals](LpSelfSimilar/Entropy/MeasurableBandConditionals.lean)

- `LpSelfSimilar.Entropy.bandIndependentCover_card_le_sixteen`
- `LpSelfSimilar.Entropy.exists_measurable_distanceBand_maximizer`
- `LpSelfSimilar.Entropy.measurable_jointLabelWeight`
- `LpSelfSimilar.Entropy.measurable_jointConditionalWeight`

### [Entropy/PosetGraphDuality](LpSelfSimilar/Entropy/PosetGraphDuality.lean)

- `LpSelfSimilar.Entropy.isIndepSet_incomparabilityGraph_iff`
- `LpSelfSimilar.Entropy.graphCoverageCost_div_eq_entropy_sub`
- `LpSelfSimilar.Entropy.graphEntropy_incomparability_add_compl`

### [Entropy/QuantizedNearEntropy](LpSelfSimilar/Entropy/QuantizedNearEntropy.lean)

- `LpSelfSimilar.Entropy.finite_probability_entropy_le_log_of_card_le`
- `LpSelfSimilar.Entropy.near_graphEntropyBits_ge_of_interval`
- `LpSelfSimilar.Entropy.dyadic_near_graphEntropyBits_ge_of_interval`

### [Entropy/SixteenAtomCancellation](LpSelfSimilar/Entropy/SixteenAtomCancellation.lean)

- `LpSelfSimilar.Entropy.sixteen_atom_entropy_le_cancellation`
- `LpSelfSimilar.Entropy.sixteen_atom_entropy_le_cancellation_log_parameter`

### [Fourier/FinitePhaseCancellation](LpSelfSimilar/Fourier/FinitePhaseCancellation.lean)

- `LpSelfSimilar.Fourier.weighted_sq_norm_finiteTransform_eq`
- `LpSelfSimilar.Fourier.weighted_sq_norm_finiteTransform_le`
- `LpSelfSimilar.Fourier.weighted_norm_finiteTransform_le_one_sub_cancellation`

### [Fourier/QuinticBandInversion](LpSelfSimilar/Fourier/QuinticBandInversion.lean)

- `LpSelfSimilar.Fourier.integrable_quinticBandProduct`
- `LpSelfSimilar.Fourier.integrable_quinticBandProductCurvature`
- `LpSelfSimilar.Fourier.angularFourier_quinticBandProduct_secondDerivative`
- `LpSelfSimilar.Fourier.quinticBandProduct_inverse_L1_bound`

### [Fourier/QuinticCutoff](LpSelfSimilar/Fourier/QuinticCutoff.lean)

- `LpSelfSimilar.Fourier.hasDerivAt_quinticBandCoordinate`
- `LpSelfSimilar.Fourier.hasDerivAt_quinticFourierCutoff`
- `LpSelfSimilar.Fourier.hasDerivAt_quinticFourierCutoffSlope`
- `LpSelfSimilar.Fourier.hasDerivAt_quinticFourierDetail`
- `LpSelfSimilar.Fourier.continuous_quinticFourierCutoffCurvature`
- `LpSelfSimilar.Fourier.quinticFourierCutoff_neg`

### [Fourier/QuinticCutoffSlopeEnergy](LpSelfSimilar/Fourier/QuinticCutoffSlopeEnergy.lean)

- `LpSelfSimilar.Fourier.integrable_sq_quinticSlopeBand`
- `LpSelfSimilar.Fourier.integral_sq_quinticSlopeBand`
- `LpSelfSimilar.Fourier.sq_quinticFourierCutoffSlope_eq_bands`
- `LpSelfSimilar.Fourier.integrable_sq_quinticFourierCutoffSlope`
- `LpSelfSimilar.Fourier.integral_sq_quinticFourierCutoffSlope`
- `LpSelfSimilar.Fourier.integral_sq_deriv_quinticFourierCutoff`

### [Fourier/QuinticCutoffSupport](LpSelfSimilar/Fourier/QuinticCutoffSupport.lean)

- `LpSelfSimilar.Fourier.quinticBandCoordinate_mem_Icc_iff`
- `LpSelfSimilar.Fourier.quinticBandCoordinate_nonpos_iff`
- `LpSelfSimilar.Fourier.one_le_quinticBandCoordinate_iff`
- `LpSelfSimilar.Fourier.quinticFourierCutoff_eq_one`
- `LpSelfSimilar.Fourier.quinticFourierCutoff_eq_zero`
- `LpSelfSimilar.Fourier.quinticFourierCutoff_eq_transition`
- `LpSelfSimilar.Fourier.hasCompactSupport_quinticFourierCutoff`

### [Fourier/QuinticDetailCurvatureIntegrals](LpSelfSimilar/Fourier/QuinticDetailCurvatureIntegrals.lean)

- `LpSelfSimilar.Fourier.ae_hasDerivAt_deriv_quinticFourierDetail`
- `LpSelfSimilar.Fourier.ae_deriv_deriv_quinticFourierDetail`
- `LpSelfSimilar.Fourier.integrable_quinticFourierDetailCurvature`
- `LpSelfSimilar.Fourier.integrable_deriv_deriv_quinticFourierDetail`
- `LpSelfSimilar.Fourier.integral_abs_deriv_deriv_quinticFourierDetail_le`
- `LpSelfSimilar.Fourier.quinticFourierDetail_integral_bounds`

### [Fourier/QuinticKernelScaleDerivative](LpSelfSimilar/Fourier/QuinticKernelScaleDerivative.lean)

- `LpSelfSimilar.Fourier.hasDerivAt_rescaled_quinticSmoothingKernel`

### [Fourier/QuinticKernelTransforms](LpSelfSimilar/Fourier/QuinticKernelTransforms.lean)

- `LpSelfSimilar.Fourier.angularFourier_quinticSmoothingKernel`
- `LpSelfSimilar.Fourier.angularFourier_quinticDetailKernel`
- `LpSelfSimilar.Fourier.integral_quinticSmoothingKernel`
- `LpSelfSimilar.Fourier.integral_quinticDetailKernel`

### [Fourier/QuinticMeanInversion](LpSelfSimilar/Fourier/QuinticMeanInversion.lean)

- `LpSelfSimilar.Fourier.sum_quinticDetail_inverse_L1_bound`
- `LpSelfSimilar.Fourier.quintic_inverse_prefactor_le`
- `LpSelfSimilar.Fourier.sum_quinticDetail_inverse_L1_le_twenty`
- `LpSelfSimilar.Fourier.integral_quinticDetail_inverse_L1_le_twenty`

### [Fourier/QuinticScaledSlopeEnergy](LpSelfSimilar/Fourier/QuinticScaledSlopeEnergy.lean)

- `LpSelfSimilar.Fourier.deriv_quinticFourierCutoff_mul`
- `LpSelfSimilar.Fourier.integrable_sq_deriv_quinticFourierCutoff_mul`
- `LpSelfSimilar.Fourier.integral_sq_deriv_quinticFourierCutoff_mul`

### [Fourier/QuinticSmoothingDensity](LpSelfSimilar/Fourier/QuinticSmoothingDensity.lean)

- `LpSelfSimilar.Fourier.exists_quintic_smoothing_density`

### [Fourier/ScaledBandShift](LpSelfSimilar/Fourier/ScaledBandShift.lean)

- `LpSelfSimilar.Fourier.bandFirstShift_spec`
- `LpSelfSimilar.Fourier.bandFirstShift_nonneg`
- `LpSelfSimilar.Fourier.bandFirstShift_dyadic`
- `LpSelfSimilar.Fourier.sixteen_pi_div_lt_fifty_two`
- `LpSelfSimilar.Fourier.shifted_band_width_lt`

### [Fourier/WeightedPlancherel](LpSelfSimilar/Fourier/WeightedPlancherel.lean)

- `LpSelfSimilar.Fourier.sq_integral_norm_angularInverseFourier_le_derivative_energy`

### [Gaussian/BinaryConditionalExpectation](LpSelfSimilar/Gaussian/BinaryConditionalExpectation.lean)

- `LpSelfSimilar.Gaussian.measurable_binaryPosteriorMean_observation`
- `LpSelfSimilar.Gaussian.integrable_binaryPosteriorMean`
- `LpSelfSimilar.Gaussian.setIntegral_binaryInputSign_eq_posterior`
- `LpSelfSimilar.Gaussian.condExp_binaryInputSign`

### [Gaussian/BinaryConditionalVariance](LpSelfSimilar/Gaussian/BinaryConditionalVariance.lean)

- `LpSelfSimilar.Gaussian.condVar_binaryInputSign`
- `LpSelfSimilar.Gaussian.integral_condVar_binaryInputSign_eq_density`
- `LpSelfSimilar.Gaussian.integral_condVar_binaryInputSign_eq_gaussian`
- `LpSelfSimilar.Gaussian.exp_neg_sq_le_integral_condVar_binaryInputSign`
- `LpSelfSimilar.Gaussian.integral_condVar_binaryInputSign_le_one`
- `LpSelfSimilar.Gaussian.hasDerivAt_binaryGaussianInformation_condVar`
- `LpSelfSimilar.Gaussian.deriv_binaryGaussianInformation_condVar`

### [Gaussian/BinaryDifferentialEntropy](LpSelfSimilar/Gaussian/BinaryDifferentialEntropy.lean)

- `LpSelfSimilar.Gaussian.integral_log_binaryGaussianDensity_gaussian`
- `LpSelfSimilar.Gaussian.integral_log_kernel_standardGaussian`
- `LpSelfSimilar.Gaussian.integrable_log_rnDeriv_standardGaussian`
- `LpSelfSimilar.Gaussian.integrable_kernel_mul_log_kernel`
- `LpSelfSimilar.Gaussian.differentialEntropy_standardGaussian`
- `LpSelfSimilar.Gaussian.integrable_log_rnDeriv_binaryGaussianLaw`
- `LpSelfSimilar.Gaussian.integrable_binaryGaussianDensity_mul_log`
- `LpSelfSimilar.Gaussian.differentialEntropy_binaryGaussianLaw`
- `LpSelfSimilar.Gaussian.binaryGaussianInformation_eq_differentialEntropy_sub`

### [Gaussian/BinaryInformationBounds](LpSelfSimilar/Gaussian/BinaryInformationBounds.lean)

- `LpSelfSimilar.Gaussian.binaryGaussianInformation_zero`
- `LpSelfSimilar.Gaussian.deriv_binaryGaussianInformation_le_self`
- `LpSelfSimilar.Gaussian.binaryGaussianInformation_le_half_sq`
- `LpSelfSimilar.Gaussian.binaryGaussianInformation_increment_lower`

### [Gaussian/BinaryInformationDecoder](LpSelfSimilar/Gaussian/BinaryInformationDecoder.lean)

- `LpSelfSimilar.Gaussian.gaussian_binary_klDiv_ne_top`
- `LpSelfSimilar.Gaussian.binaryGaussianInformation_ge_sign_entropy`
- `LpSelfSimilar.Gaussian.binaryGaussianInformation_two_lower`
- `LpSelfSimilar.Gaussian.binaryGaussianInformation_two_div_le`
- `LpSelfSimilar.Gaussian.binaryGaussianInformation_high_scale_margin`
- `LpSelfSimilar.Gaussian.exists_binaryGaussianInformation_half_gain`

### [Gaussian/BinaryInformationScaling](LpSelfSimilar/Gaussian/BinaryInformationScaling.lean)

- `LpSelfSimilar.Gaussian.gaussianEntropyProfile_le_information_increment`
- `LpSelfSimilar.Gaussian.three_tenths_le_information_increment`
- `LpSelfSimilar.Gaussian.exists_binaryGaussianInformation_scaling_gain`

### [Gaussian/BinaryProbabilitySpace](LpSelfSimilar/Gaussian/BinaryProbabilitySpace.lean)

- `LpSelfSimilar.Gaussian.measurable_binaryInputSign`
- `LpSelfSimilar.Gaussian.binaryInputSign_sq`
- `LpSelfSimilar.Gaussian.measurable_binaryGaussianOutput`
- `LpSelfSimilar.Gaussian.binaryGaussianObservation_le`
- `LpSelfSimilar.Gaussian.binaryGaussianInput_map_noise`
- `LpSelfSimilar.Gaussian.binaryGaussianInput_map_sign`
- `LpSelfSimilar.Gaussian.binaryInputSign_indep_noise`
- `LpSelfSimilar.Gaussian.binaryGaussianInput_map_output`
- `LpSelfSimilar.Gaussian.memLp_binaryInputSign`
- `LpSelfSimilar.Gaussian.integrable_binaryInputSign`

### [Gaussian/EvenMoments](LpSelfSimilar/Gaussian/EvenMoments.lean)

- `LpSelfSimilar.Gaussian.integrable_gaussian_even_moment`
- `LpSelfSimilar.Gaussian.gamma_eq_two_mul_integral_gaussian_even_moment`
- `LpSelfSimilar.Gaussian.integral_gaussian_even_moment`

### [Gaussian/LowFrequencyConstant](LpSelfSimilar/Gaussian/LowFrequencyConstant.lean)

- `LpSelfSimilar.Gaussian.integrable_lowFrequencyGaussianEnergy`
- `LpSelfSimilar.Gaussian.integral_lowFrequencyGaussianEnergy`
- `LpSelfSimilar.Gaussian.lowFrequencyGaussianConstant_eq`
- `LpSelfSimilar.Gaussian.sqrt_pi_lt_1773_div_1000`
- `LpSelfSimilar.Gaussian.lowFrequencyGaussianConstant_lt_1709_div_1000`
- `LpSelfSimilar.Gaussian.lowFrequencyGaussianConstant_lt_seven_fourths`

### [Gaussian/ScaledTailEnergy](LpSelfSimilar/Gaussian/ScaledTailEnergy.lean)

- `LpSelfSimilar.Gaussian.scaled_highFrequency_subset_abs_tail`
- `LpSelfSimilar.Gaussian.half_integral_standardGaussian_scaled_tail_energy_le`

### [Gaussian/TailMoments](LpSelfSimilar/Gaussian/TailMoments.lean)

- `LpSelfSimilar.Gaussian.integrable_id_mul_exp_neg_sq`
- `LpSelfSimilar.Gaussian.tendsto_pow_mul_exp_neg_sq_zero`
- `LpSelfSimilar.Gaussian.integral_Ioi_id_mul_exp_neg_sq`
- `LpSelfSimilar.Gaussian.integral_Ioi_exp_neg_sq_le`
- `LpSelfSimilar.Gaussian.integral_Ioi_sq_mul_exp_neg_sq`
- `LpSelfSimilar.Gaussian.integral_Ioi_sq_mul_exp_neg_sq_le`

### [Geometry/FiniteIntervalQuantization](LpSelfSimilar/Geometry/FiniteIntervalQuantization.lean)

- `LpSelfSimilar.Geometry.exists_finite_interval_quantization`

### [Rational/CubicContinuity](LpSelfSimilar/Rational/CubicContinuity.lean)

- `LpSelfSimilar.rational_bernoulli_convolution_continuous_density_cubic`

### [Rational/CubicIntegerFamily](LpSelfSimilar/Rational/CubicIntegerFamily.lean)

- `LpSelfSimilar.bernoulli_convolution_one_sub_inv_continuous_density_cubic`
- `LpSelfSimilar.bernoulli_convolution_one_sub_inv_continuous_density_cubic_int`

### [Rational/CubicParameters](LpSelfSimilar/Rational/CubicParameters.lean)

- `LpSelfSimilar.Rational.cubic_gap_parameter_invariants`
- `LpSelfSimilar.Rational.rational_cubic_hypothesis`

### [SelfSimilar/Concentration/ExactModulus](LpSelfSimilar/SelfSimilar/Concentration/ExactModulus.lean)

- `LpSelfSimilar.SelfSimilar.Concentration.smallSetMass_exact_concentration_recurrence`

### [SelfSimilar/Concentration/PowerBounds](LpSelfSimilar/SelfSimilar/Concentration/PowerBounds.lean)

- `LpSelfSimilar.SelfSimilar.Concentration.concentration_mass_power_bound`
- `LpSelfSimilar.SelfSimilar.Concentration.concentration_mass_and_density_power_bounds`

### [SelfSimilar/Concentration/PowerL2](LpSelfSimilar/SelfSimilar/Concentration/PowerL2.lean)

- `LpSelfSimilar.SelfSimilar.Concentration.memLp_two_of_small_set_bound_via_layercake`

### [SelfSimilar/Concentration/SharpL2](LpSelfSimilar/SelfSimilar/Concentration/SharpL2.lean)

- `LpSelfSimilar.SelfSimilar.Concentration.memLp_two_of_small_set_bound`
