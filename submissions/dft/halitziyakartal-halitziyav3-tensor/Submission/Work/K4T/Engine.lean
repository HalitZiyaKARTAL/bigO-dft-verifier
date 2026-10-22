import Submission.Work.K4T.RawCert
import Submission.Work.K4T.TensorG
-- changed for the tensor-power extension (26159999/10000000000); see Submission.lean

/-!
# THE engine theorem of the instance K4T (Route B: tensor power of the RAW P4-L-fresh unit)

`MX.K4T.engine : MX.K4T.EngineStmt.{0}`: OpenAI's `hills_program` statement at the seam exponent
`1 - 2615999999/10^12` (DFT figure 2.6159999e-3), from the RAW certificate with `G` copies (`PB.K4T.RawCertG`, at
present the declared hole H2 `PB.K4T.hole_rawCertG`) and the tensor engine `PB.K4T.tensorEngineG` (K4T/TensorG.lean:
the tensor agent's `TensorEng.k4f_engine_of_rawG`).
-/

namespace OAI
namespace PowerSaving
namespace MX
namespace K4T

/-- **THE ENGINE THEOREM OF K4T.** -/
theorem engine : EngineStmt.{0} := by
  obtain ⟨α, ρ, σ, i1, i2, i3, i4, i5, i6, hc⟩ := PB.K4T.rawCertG_ex
  exact @PB.K4T.tensorEngineG α ρ σ i1 i2 i3 i4 i5 i6 hc

end K4T
end MX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.MX.K4T.engine
