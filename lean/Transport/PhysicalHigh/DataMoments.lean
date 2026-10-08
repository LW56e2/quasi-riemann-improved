import Transport.PhysicalHigh.ChosenMoments
import Transport.PhysicalHigh.MomentBound

namespace RH.Transport.PhysicalHigh
noncomputable section
open scoped Classical
open Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbeFinalAssembly ProbeHighRowFamily HeckeInverseAmplification

theorem data_chosen_moments {Δ : ℝ} {seed : Parameters.HighData Δ} (F : SourceData seed)
    {Kmin : ℕ} {allowance : ℝ} (D : TunedData Kmin allowance)
    (counts : CountParameters F.modulus ⊤ reservedLoss)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta≤7/8) :
    ∃τ : ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.P.cost ∧
      τ<reservedLoss ∧ 2*τ≤reservedLoss ∧ τ*(2+4*D.P.eps)<reservedLoss ∧
      ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
        1<Z ∧ TunedSourceMomentBound F D counts η Z τ (C*Z^reservedLoss) (Z^(2*τ)) := by
  exact actual_chosen_moments F D.K D.ell D.slots_pos D.slots_injective
    reservedLoss D.rmin D.ellMin allowance reservedLoss_pos reservedLoss_le_one D.P
    D.slots_fine counts.cB counts.kB counts.cH counts.kH
    counts.cB_pos counts.kB_pos counts.cH_pos counts.kH_pos hbeta hceiling

end
end RH.Transport.PhysicalHigh
