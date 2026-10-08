import Transport.PhysicalHigh.SourceMomentsCore
import Transport.PhysicalHigh.PlainInputs
import Transport.PhysicalHigh.PlainUnmarked
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorMoments

namespace RH.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainUnmarkedField
local notation "O"=>HeckeFamily.O

/-- Actual raw fiber moments at fixed kappa=3/4, for every finite collection
of sufficiently fine positive distinct slots. The old geometry carried by
`F : SourceData D` is not used. All four `Moments` fields are proved from
OpenAI003 arithmetic/energy theorems under the accepted family ceiling. -/
theorem actual_source_moments {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (N:ℕ)(ell:Fin N→ℝ)(hell:∀j,0<ell j)(hinj:Function.Injective ell)
    (ε εm:ℝ)(hε:ε≤1/1000)(hεm:0<εm)(hεm1:εm≤1)
    (hfine:∀j,ell j≤plainMesh εm/200)
    (cB kB cH kH:ℝ)(hcB:0<cB)(hkB:0<kB)(hcH:0<cH)(hkH:0<kH)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hceiling:HeckeZeroSupremum.beta≤7/8):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
      1<Z ∧ ∀height:ℝ,0≤height→∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→∀d:ℝ,(1/200:ℝ)≤d→
      ∀a τ dmax slotMesh binWidth:ℝ,∀i:ℕ,∀z:ℂ,z.re=17/50→|z.im|≤height→
      SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows ell
        (fun _ y=>(F.w y:ℂ)) Z d a ε τ dmax 2 slotMesh binWidth i z 0
        (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then kB else kH)
        (C*(1+height)^J) height εm :=by
  exact actual_source_moments_from_inputs F N ell hell hinj ε εm hε hεm hεm1 hfine
    cB kB cH kH hcB hkB hcH hkH (actual_plain_inputs F N εm hεm hbeta hceiling)

end
end RH.Transport.PhysicalHigh
