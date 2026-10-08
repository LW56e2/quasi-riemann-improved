import OAI.NumberTheory.DirichletL.Energy.WidthRanges

namespace RH.Transport.PhysicalHigh
noncomputable section
open OAI OAI.SevenEighths
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

def plainMesh (εm:ℝ):ℝ:=fineMesh 2 0 1 (3/4) (εm/4)

lemma plainMesh_pos {εm:ℝ}(hεm:0<εm):0<plainMesh εm:=by
  exact (bounds 2 (finalSourceCap 2 0 1 (εm/4)) (3/4) (εm/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by norm_num) (by positivity)).2.2.2.2.1

end
end RH.Transport.PhysicalHigh
