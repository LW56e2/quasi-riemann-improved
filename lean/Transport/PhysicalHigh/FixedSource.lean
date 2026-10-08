import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport

/-!
# Fixed source arithmetic data for an arbitrary actual error

The upstream SourceData record is indexed by HighData. Here HighData(1) is
only an auxiliary carrier for that existing record: none of its geometric
parameters are the tuned probe's parameters. Both required tail bounds are
obtained from one sufficiently large finite prime exclusion set. All later
moment theorems use independently specified actual slots and errors.
-/

namespace RH.Transport.PhysicalHigh
noncomputable section
open scoped Classical ContDiff
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeFinalAssembly Parameters
local notation "O" => HeckeFamily.O

/-- The arithmetic carrier exists for every actual positive error and every
specified finite set of prime exclusions. No hypothesis about beta is used. -/
theorem exists_tuned_source_data (e : ℝ) (he : 0 < e)
    (S₀ : Finset (Ideal O)) (hS₀ : ∀ P ∈ S₀, Prime P) :
    ∃ D : HighData (1 : ℝ), ∃ F : SourceData D,
      S₀ ⊆ F.S ∧ FirstTail (4 * e) F.S := by
  obtain ⟨D⟩ := exists_high_data (1 : ℝ) (by norm_num)
  obtain ⟨S,hsub,hS,hfirst,hmax⟩ :=
    exists_fixed_source (min e D.e) (lt_min he D.e_pos) S₀ hS₀
  have hseed : FirstTail (4 * D.e) S :=
    hfirst.mono_parameter (by linarith [min_le_right e D.e])
  have hactual : FirstTail (4 * e) S :=
    hfirst.mono_parameter (by linarith [min_le_left e D.e])
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,heq,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
  let F : SourceData D :=
    ⟨S,hS,hmax,hseed,w,W,hw,hc,hs,hp,hb,hn,heq,hWn,hWs,hr,hWpos⟩
  exact ⟨D,F,hsub,hactual⟩

/-- The count constants are chosen at the actual reserved moment loss t,
before the moment degree and height exponent are selected. -/
theorem exists_tuned_count_parameters {Δ : ℝ} {D : HighData Δ}
    (F : SourceData D) (t : ℝ) (ht : 0 < t) :
    Nonempty (CountParameters F.modulus ⊤ t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x => (F.bounded x).1) F.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) F.support
    (fun x => (F.bounded x).2) t ht

end
end RH.Transport.PhysicalHigh
