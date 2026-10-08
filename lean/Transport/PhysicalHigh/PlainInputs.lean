import Transport.PhysicalHigh.PlainInputExtract
import Transport.PhysicalHigh.PlainEnergy

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

/-- The required positive and zero arithmetic energy inputs are produced
from the actual proved OpenAI003 energy induction under the accepted ceiling. -/
theorem actual_plain_inputs {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (N:ℕ)(εm:ℝ)(hεm:0<εm)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hceiling:HeckeZeroSupremum.beta≤7/8):
    PositiveFineSourceInput F N εm (plainMesh εm) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (εm/4) U degree control A):=by
  apply plain_inputs F N εm hεm
  intro bΦ hbΦ
  exact actual_plain_energy_fixed_kappa (Slot:=Fin N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x)) (CenteredMomentDetectorPlainSlotProfile.conjugate_source_support F)
    (Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)) bΦ (εm/4) hbΦ (by positivity)
    hbeta hceiling

end
end RH.Transport.PhysicalHigh
