import Transport.PhysicalAnalytic.PrincipalCorrection
import Transport.PhysicalAnalytic.GlobalCorrection
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement

/-!
# The actual source correction with transported exclusions

The excluded set contains both the source's required bad primes and the
transported principal-product cutoff. The correction is the literal
PrincipalSignalComparison.sourceCorrection, and finite deletion uses the
source's actual excluded-prime character.
-/

namespace RH.Transport.PhysicalAnalytic

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ActualEisensteinCubic ProbeEuler ProbePhysical HeckeFamily
open PrincipalSignalComparison
local notation "O" => ActualEisensteinCubic.O

/-- Preserve all source exclusions while adding the new uniform cutoff. -/
theorem exists_transported_source_exclusions
    (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 1000)
    (S₀ : Finset (Ideal O)) (hprime : ∀ P ∈ S₀, Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S₀) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧ SourceExclusions S ∧
      ∀ η : Character,
        AnalyticOnNhd ℂ (sourceCorrection η S)
          {s : ℂ | Geometry.boundary p < s.re} ∧
        ∀ s : ℂ, Geometry.boundary p < s.re →
          ‖sourceCorrection η S s - 1‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨N, _, hcut⟩ := exists_uniform_transported_principal_cutoff p hp0 hp
  let S₁ := S₀ ∪ smallPrimeSet N
  have hprime₁ : ∀ P ∈ S₁, Prime P := by
    intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact hprime P hP
    · exact (Finset.mem_filter.mp hP).2
  have hbad₁ : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S₁ :=
    hbad.trans Finset.subset_union_left
  obtain ⟨S, hsub, hS⟩ := exists_source_exclusions S₁ hprime₁ hbad₁
  refine ⟨S, Finset.subset_union_left.trans hsub, hS, ?_⟩
  have hN : ∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S := by
    intro P hP
    exact hsub (Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP))
  intro η
  simpa only [sourceCorrection_eq_principal η S hS] using hcut S hN η

/-- The coefficient mask is exact; analyticity and contraction are supplied by
the preceding concrete Euler-product construction. -/
theorem transported_actual_source_analytic
    (p : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hanalytic : ∀ η : Character,
      AnalyticOnNhd ℂ (sourceCorrection η S)
        {s : ℂ | Geometry.boundary p < s.re} ∧
      ∀ s : ℂ, Geometry.boundary p < s.re →
        ‖sourceCorrection η S s - 1‖ ≤ (1 / 2 : ℝ))
    (η : Character) :
    (∀ I, idealCoeff (η.excludePrimes S hS.prime) I =
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S)
      {s : ℂ | Geometry.boundary p < s.re} ∧
    (∀ s : ℂ, Geometry.boundary p < s.re →
      ‖sourceCorrection η S s - 1‖ ≤ (1 / 2 : ℝ)) :=
  ⟨excludePrimes_mask η S hS.prime, hanalytic η⟩

/-- The old source tail hypothesis already suffices on the transported domain:
the broad local Euler estimate retains the same summable majorant. -/
theorem sourceCorrection_transported_analytic
    (p : ℝ) (hp : p < 1 / 1000) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (η : Character) :
    AnalyticOnNhd ℂ (sourceCorrection η S)
      {s : ℂ | Geometry.boundary p < s.re} := by
  change AnalyticOnNhd ℂ (fun s => globalClosedCorrection η S s 1 (1 / 6))
    {s : ℂ | Geometry.boundary p < s.re}
  exact globalClosedCorrection_transported_analytic_x p hp η S hS.tail
      (1 : ℂ) (1 / 6 : ℂ) (by norm_num) (by norm_num)

theorem sourceCorrection_transported_bound
    (p : ℝ) (hp : p < 1 / 1000) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (η : Character) (s : ℂ)
    (hs : Geometry.boundary p < s.re) :
    ‖sourceCorrection η S s - 1‖ ≤ (1 / 2 : ℝ) :=
  globalClosedCorrection_transported_bound p hp η S hS.tail
    s 1 (1 / 6) hs.le (by norm_num) (by norm_num)

/-- No extra correction hypothesis or enlarged exclusion set is needed. -/
theorem actual_source_analytic_transported
    (p : ℝ) (hp : p < 1 / 1000) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (η : Character) :
    (∀ I, idealCoeff (η.excludePrimes S hS.prime) I =
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S)
      {s : ℂ | Geometry.boundary p < s.re} ∧
    (∀ s : ℂ, Geometry.boundary p < s.re →
      ‖sourceCorrection η S s - 1‖ ≤ (1 / 2 : ℝ)) :=
  ⟨excludePrimes_mask η S hS.prime,
    sourceCorrection_transported_analytic p hp S hS η,
    sourceCorrection_transported_bound p hp S hS η⟩

end
end RH.Transport.PhysicalAnalytic
