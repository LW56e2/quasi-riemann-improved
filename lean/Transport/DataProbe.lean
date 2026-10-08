import Transport.PhysicalLow.NormalizedProbe
import Transport.PhysicalHigh.TunedData
import Transport.PhysicalHigh.FixedSource

namespace RH.Transport
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeFinalAssembly

/-- One literal normalized physical probe, shared by the low and high proofs. -/
def dataProbe {Δ : ℝ} {seed : Parameters.HighData Δ} (F : SourceData seed)
    {Kmin : ℕ} {allowance : ℝ} (D : PhysicalHigh.TunedData Kmin allowance)
    (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  PhysicalLow.tunedNormalizedProbe F.modulus ⊤ F.S F.maximal D.ell 1 2
    (fun _=>F.w) F.W F.W η

theorem dataProbe_low {Δ : ℝ} {seed : Parameters.HighData Δ} (F : SourceData seed)
    {Kmin : ℕ} {allowance : ℝ} (D : PhysicalHigh.TunedData Kmin allowance)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    dataProbe F D η=O[atTop](fun Z : ℝ=>Z^(TunedCandidate.signal TunedCandidate.B+loss)) := by
  exact PhysicalLow.transport_tunedNormalizedProbe_low F.modulus ⊤ le_top
    F.S F.exclusions F.maximal 1 2 1 loss (by norm_num) (by norm_num) hloss
    D.ell D.slots_pos D.slots_injective D.slots_sum (fun _=>F.w)
    (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2
    (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero η

end
end RH.Transport
