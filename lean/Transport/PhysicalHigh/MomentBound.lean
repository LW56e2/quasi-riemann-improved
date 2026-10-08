import Transport.PhysicalHigh.TunedData
import Transport.PhysicalHigh.FixedSource
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput

namespace RH.Transport.PhysicalHigh
noncomputable section
open scoped Classical
open Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbeFinalAssembly ProbeHighRowFamily HeckeInverseAmplification

/-- Actual moment fields for all row subsets needed by the central partition. -/
def TunedSourceMomentBound {Δ : ℝ} {seed : Parameters.HighData Δ} (F : SourceData seed)
    {Kmin : ℕ} {allowance : ℝ} (D : TunedData Kmin allowance)
    (counts : CountParameters F.modulus ⊤ reservedLoss)
    (η : Character) (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
  ∀d : ℝ,(1/200:ℝ)≤d→∀a dmax slotMesh binWidth : ℝ,∀i : ℕ,∀z : ℂ,
  z.re=17/50→|z.im|≤height→
  SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
    (fun _ y=>(F.w y:ℂ)) Z d a D.P.ε τ dmax 2 slotMesh binWidth i z 0
    (if 2*a-1≤5/6 then counts.cB else counts.cH)
    (if 2*a-1≤5/6 then counts.kB else counts.kH) C height reservedLoss


end
end RH.Transport.PhysicalHigh
