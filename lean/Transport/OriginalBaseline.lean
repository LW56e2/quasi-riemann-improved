import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

/-! The original family boundary, obtained from the pinned complete OpenAI
proof. No new axiom or nonvanishing hypothesis is introduced here. -/

namespace RH.Transport

theorem original_hecke_boundary :
    OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ) := by
  exact OAI.SevenEighths.HeckeCommonProbe.beta_le_seven_eighths
    (OAI.SevenEighths.ProbeFinalAssembly.common_probe_of_chosen_moments
      (OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        OAI.SevenEighths.ProbeFinalAssemblyUnconditional.detector_certified_bands))

end RH.Transport
