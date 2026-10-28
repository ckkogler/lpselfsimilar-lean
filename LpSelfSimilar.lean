module

public import LpSelfSimilar.Rational.ExplicitContinuousDensity
public import LpSelfSimilar.Algebraic.HigherIntegrability
public import LpSelfSimilar.Algebraic.BlockVariance
public import LpSelfSimilar.Algebraic.ArithmeticInput
public import LpSelfSimilar.Algebraic.ContractingConjugates
public import LpSelfSimilar.Algebraic.MatrixDigitEntropy
public import LpSelfSimilar.Entropy.AdditiveInformationChain
public import LpSelfSimilar.Entropy.SignalEntropyBound
public import LpSelfSimilar.Entropy.AdditiveInformationEquiv
public import LpSelfSimilar.Algebraic.HeightPowers
public import LpSelfSimilar.Algebraic.ComplexityPowers
public import LpSelfSimilar.Algebraic.GridEntropy
public import LpSelfSimilar.Algebraic.GapEstimate
public import LpSelfSimilar.Algebraic.RationalIdentification
public import LpSelfSimilar.Entropy.RandomGridVariance
public import LpSelfSimilar.Probability.DiscreteConditionalLaw
public import LpSelfSimilar.Gaussian.SharpIntegratingDetail
public import LpSelfSimilar.Gaussian.GeneralConditionalVariance
public import LpSelfSimilar.Gaussian.KernelConditionalGroup
public import LpSelfSimilar.Probability.RealConditionalVariance
public import LpSelfSimilar.Bernoulli.SharpWeakSmoothing
public import LpSelfSimilar.Gaussian.ExactNormalization
public import LpSelfSimilar.Rational.ContinuousDensity
public import LpSelfSimilar.Rational.HigherIntegrability
public import LpSelfSimilar.Rational.BoundedApproximation
public import LpSelfSimilar.Bernoulli.BlockDetail
public import LpSelfSimilar.Bernoulli.BlockWindows
public import LpSelfSimilar.Rational.VarianceGrid
public import LpSelfSimilar.Gaussian.IntegratingDetail
public import LpSelfSimilar.Entropy.GridDetail
public import LpSelfSimilar.Gaussian.ConditionalVarianceGroup
public import LpSelfSimilar.Probability.TotalConditioning
public import LpSelfSimilar.Analysis.VarianceGrouping
public import LpSelfSimilar.Gaussian.MixtureDetail
public import LpSelfSimilar.Bernoulli.WeakSmoothing
public import LpSelfSimilar.Gaussian.SmallSummandsGeneral
public import LpSelfSimilar.Gaussian.TranslationRemainder
public import LpSelfSimilar.Analysis.RemainderMoments
public import LpSelfSimilar.Rational.BlockVariance
public import LpSelfSimilar.Gaussian.Semigroup
public import LpSelfSimilar.WeakReverseHolder
public import LpSelfSimilar.SelfSimilar.HigherIntegrability
public import LpSelfSimilar.Bernoulli.ConvolutionPowers
public import LpSelfSimilar.Rational.Parameters
public import LpSelfSimilar.Rational.GridEntropy
public import LpSelfSimilar.Bernoulli.FiniteBounds
public import LpSelfSimilar.Gaussian.IntegratingScales
public import LpSelfSimilar.Gaussian.SmoothingMeasure
public import LpSelfSimilar.Entropy.Collision
public import LpSelfSimilar.Entropy.GridBounds
public import LpSelfSimilar.Analysis.RandomGrid
public import LpSelfSimilar.Entropy.CellEntropyVariance
public import LpSelfSimilar.Entropy.ConditionalStatistic
public import LpSelfSimilar.Entropy.EntropyVariance

public import LpSelfSimilar.Algebraic.ContinuousDensityEndpoint

@[expose] public section

/-!
Public library root. Exposes Lemma 2.1 (`LpSelfSimilar.weak_reverse_holder`)
Theorem 1.1 (`LpSelfSimilar.self_similar_higher_integrability`), and Corollary 1.3
(`LpSelfSimilar.bernoulli_convolution_continuous_density`), together with
the reusable Gaussian, entropy, probability and rational arithmetic machinery
used in the rational proof of Corollary 1.3.
-/
